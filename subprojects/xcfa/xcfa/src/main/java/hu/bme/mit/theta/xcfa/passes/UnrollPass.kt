/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.*
import java.util.*
import kotlin.random.Random

/**
 * Unrolls loops where the number of loop executions can be determined statically. The UNROLL_LIMIT
 * refers to the number of loop executions: loops that are executed more times than this limit are
 * not unrolled. Loops with unknown number of iterations are unrolled to FORCE_UNROLL_LIMIT
 * iterations (this way a safe result might not be valid). Recursive calls are expanded the same
 * way, to UNROLL_RECURSION_LIMIT.
 *
 * @param substituteLoopVar when true, each unrolled copy has the loop variable replaced by its
 *   constant value for that iteration (`&t[i]` becomes `&t[0]`, `&t[1]`, …). Only the loop variable
 *   is substituted, so address-of expressions of other variables (`&x`) are left for
 *   ReferenceElimination -- which is why this may safely run before it. Requires [parseContext].
 *
 *   This duplicates constant propagation, and could be dropped if [SimplifyExprsPass] ran after
 *   [PthreadArrayHandleUnrollPass] instead -- but no pass order allows that. Simplification has to
 *   come after [ReferenceElimination], or it folds the variable naming an object into that object's
 *   base id and every later pass that matches on the variable stops recognising the object.
 *   [ReferenceElimination] in turn has to come after [AtomicFunctionsPass], [LibraryStubsPass] and
 *   [CLibraryFunctionsPass], which all read `&x` arguments as references. [CLibraryFunctionsPass]
 *   cannot move after it at all: an address-taken local is re-based onto a runtime counter, leaving
 *   a thread handle with no static identity to match a create to its join. Removing this parameter
 *   therefore means giving handles an identity that survives re-basing, not reordering passes.
 *
 * @param cutBounds per-cut-point overrides of the force unroll and recursion bounds
 * @param markUnrollExits whether cut-off continuations lead into [unroll exit locations][UnrollCut]
 */
class UnrollPass(
  specificForceUnrollLimit: Int? = null,
  specificRecursionUnrollLimit: Int? = null,
  private val substituteLoopVar: Boolean = false,
  private val parseContext: ParseContext? = null,
  private val cutBounds: Map<String, Int> = emptyMap(),
  private val markUnrollExits: Boolean = false,
) : ProcedurePass {

  companion object {

    var UNROLL_LIMIT = 1000
    var FORCE_UNROLL_LIMIT = -1

    /**
     * How deep recursive calls left over after inlining are expanded (-1 to leave them alone).
     *
     * This lives here rather than in [InlineProceduresPass] on purpose. Inlining runs once, up
     * front, and gives up entirely on a procedure that (transitively) reaches recursion --
     * `canInline` is all-or-nothing, so one recursive callee leaves *every* call in that procedure
     * un-inlined. A backend that raises its bound and re-runs (the OC checker escalates its bound
     * until a safe result is no longer bound-limited) therefore gets no benefit from it. Expanding
     * here means each new bound re-expands the recursion to the new depth, and the result is marked
     * unsafe-unroll exactly like a force-unrolled loop, so a `safe` verdict stays flagged as
     * bound-limited.
     */
    var UNROLL_RECURSION_LIMIT = -1

    /**
     * Replace a loop that only waits for a condition with a single iteration of itself.
     *
     * Off by default: it is exact for reachability but not for termination and a program without
     * a waiting loop has nothing for it to change.
     */
    var COLLAPSE_BUSY_WAITS = false

    /**
     * Random generator for the order [findLoop] explores edges in.
     *
     * Which loop the search happens to reach first decides which loops get taken apart and which
     * are left for the fallbacks; set this to vary the exploration deliberately. Prefer setting
     * the random in the config-to-checker utilities (see [ConfigToCegarChecker]).
     */
    var random = Random.Default

    private val transFunc: ExplStmtTransFunc by lazy {
      val solver = Z3SolverFactory.getInstance().createSolver()
      ExplStmtTransFunc.create(solver, 1)
    }
  }

  private val forceUnrollLimit = specificForceUnrollLimit ?: FORCE_UNROLL_LIMIT

  private val recursionUnrollLimit = specificRecursionUnrollLimit ?: UNROLL_RECURSION_LIMIT

  private val collapseBusyWaits = COLLAPSE_BUSY_WAITS

  /** The program's global variables, i.e. the ones another thread can observe. */
  private var globalVars: Set<VarDecl<*>> = emptySet()

  private val testedLoops = mutableSetOf<Loop>()

  private val unusedLocRemovalPass = UnusedLocRemovalPass()

  /**
   * Which procedures are recursive, decided once for the whole program.
   *
   * The pass instance is reused across procedures, and expanding a call rewrites the *callee's*
   * body in place, so asking again once some bodies have already been expanded gives a different --
   * and order-dependent -- answer. Recursion is a property of the program as it arrived, so it is
   * settled on first use and kept.
   */
  private var recursiveProcedures: Set<String>? = null

  private val tracker = CutTracker()

  /**
   * Maps every copied location (by identity) to its input location, so all copies of a loop share
   * one [UnrollCut] key. Also creates the exit locations.
   */
  private inner class CutTracker {

    private val origins = IdentityHashMap<XcfaLocation, XcfaLocation>()

    private fun origin(loc: XcfaLocation): XcfaLocation = origins[loc] ?: loc

    fun copied(copy: XcfaLocation, of: XcfaLocation) {
      origins[copy] = origin(of)
    }

    fun key(kind: UnrollCut, builder: XcfaProcedureBuilder, loc: XcfaLocation) =
      kind.key(builder.name, origin(loc).name)

    fun bound(key: String, default: Int): Int = if (default == -1) -1 else cutBounds[key] ?: default

    fun cut(
      builder: XcfaProcedureBuilder,
      key: String,
      source: XcfaLocation,
      labels: List<XcfaLabel>,
      metadata: MetaData,
    ) {
      if (!markUnrollExits) return
      val name = UnrollCut.locationName(key)
      val exit =
        builder.getLocs().find { it.name == name }
          ?: XcfaLocation(name, metadata = EmptyMetaData).also(builder::addLoc)
      // only the condition of the cut-off step matters: its other effects would just add events
      labels.forEach { label ->
        val condition = label.getFlatLabels().takeWhile { it is StmtLabel && it.stmt is AssumeStmt }
        builder.addEdge(XcfaEdge(source, exit, SequenceLabel(condition), metadata))
      }
    }
  }

  private data class Loop(
    val loopStart: XcfaLocation,
    val loopCondStart: XcfaLocation,
    val loopLocs: Set<XcfaLocation>,
    val loopEdges: Set<XcfaEdge>,
    val loopVar: VarDecl<*>?,
    val loopVarInit: XcfaEdge?,
    val loopVarModifiers: List<XcfaEdge>?,
    val loopStartEdges: List<XcfaEdge>,
    val exitEdges: Map<XcfaLocation, List<XcfaEdge>>,
    val properlyUnrollable: Boolean,
    val forceUnrollLimit: Int,
    val substituteLoopVar: Boolean = false,
    val parseContext: ParseContext? = null,
    val exitKey: String,
    private val tracker: CutTracker,
    val collapseBusyWaits: Boolean = false,
    val globalVars: Set<VarDecl<*>> = emptySet(),
  ) {

    /** The loop variable's value at each iteration, filled by [count] when [substituteLoopVar]. */
    private val loopVarValues = mutableListOf<LitExpr<*>>()

    private class BasicStmtAction(private val stmt: Stmt) : StmtAction() {
      constructor(edge: XcfaEdge) : this(edge.label.toStmt())

      constructor(edges: List<XcfaEdge>) : this(SequenceLabel(edges.map { it.label }).toStmt())

      override fun getStmts() = listOf(stmt)
    }

    fun unroll(builder: XcfaProcedureBuilder, forceLimit: Int = forceUnrollLimit): Boolean {
      val c = count()
      if (c != null) {
        unroll(builder, c, !isBusyWait)
        return true
      } else if (forceLimit != -1) {
        builder.setUnsafeUnroll()
        val next = unroll(builder, forceLimit, false)
        // no entry edge to copy the condition from: the next iteration starts unconditionally
        val entries = loopStartEdges.map { it.label }.ifEmpty { listOf(SequenceLabel(listOf())) }
        val metadata = loopStartEdges.firstOrNull()?.metadata ?: EmptyMetaData
        tracker.cut(builder, exitKey, next, entries, metadata)
        return true
      }
      return false
    }

    /** Returns the location where the iteration after the last copy would start. */
    fun unroll(builder: XcfaProcedureBuilder, count: Int, removeCond: Boolean): XcfaLocation {
      // Save loopStart->...->loopCondStart path for finish (to preserve metadata)
      val metadataEdges = mutableListOf<XcfaEdge>()
      var loc = loopStart
      while (loc != loopCondStart) {
        check(loc.outgoingEdges.size == 1)
        val edge = loc.outgoingEdges.first()
        check(edge.label.getFlatLabels().isEmpty())
        metadataEdges.add(edge)
        loc = edge.target
      }

      // Remove original loop locations and edges
      (loopLocs - loopStart).forEach(builder::removeLoc)
      loopLocs.flatMap { it.outgoingEdges }.forEach(builder::removeEdge)

      // Copy loop body `count` times
      var startLocation = loopStart
      for (i in 0 until count) {
        startLocation = copyBody(builder, startLocation, i, removeCond)
      }

      // Finish loop
      exitEdges[loopCondStart]?.let { loopExitEdges ->
        metadataEdges.forEach { metadataEdge ->
          val oldTarget = metadataEdge.target
          val newLoc = XcfaLocation("${oldTarget.name}_loop_exit", metadata = oldTarget.metadata)
          tracker.copied(newLoc, oldTarget)
          val newEdge = XcfaEdge(startLocation, newLoc, metadataEdge.label, metadataEdge.metadata)
          builder.addEdge(newEdge)
          startLocation = newLoc
        }
        loopExitEdges.forEach { edge ->
          val label = if (removeCond) edge.label.removeCondition() else edge.label
          builder.addEdge(XcfaEdge(startLocation, edge.target, label, edge.metadata))
        }
      }

      // Only the *outgoing* edges of the loop locations were removed above, so an edge that came
      // into the middle of the body from outside it -- which nested and repeated unrolling of the
      // same region does produce -- is left pointing at a location that no longer exists. It can
      // never be taken again either way (its target is gone), but left in the edge set it breaks
      // every consumer that maps edges through the procedure's locations: `XcfaProcedure.deepCopy`
      // dies on a bare `!!`, with nothing to say which pass was responsible. Drop them here, at the
      // point the locations went away.
      builder
        .getEdges()
        .filter { it.source !in builder.getLocs() || it.target !in builder.getLocs() }
        .forEach(builder::removeEdge)
      return startLocation
    }

    private fun count(): Int? {
      if (isBusyWait) return 1

      if (!properlyUnrollable) return null
      check(loopVar != null && loopVarModifiers != null && loopVarInit != null)
      check(loopStartEdges.size == 1)

      // Counting the iterations means asking a solver to evaluate these statements, and the
      // dereferences the frontend emits carry no `uniquenessIdx` -- which every solver transformer
      // rejects outright ("Incomplete dereferences ... are not handled properly"). That index is
      // added later, and only on the CEGAR path (`PtrUtils.uniqueDereferences`, driven by
      // `PtrAction`), so a pass running before it must not hand a dereference to the solver at all.
      // A loop whose trip count touches memory therefore counts as "not statically known".
      if (
        (loopStartEdges + loopVarModifiers + loopVarInit).any { it.label.dereferences.isNotEmpty() }
      )
        return null

      val prec = ExplPrec.of(listOf(loopVar))
      var state = ExplState.of(ImmutableValuation.empty())
      state = transFunc.getSuccStates(state, BasicStmtAction(loopVarInit), prec).first()

      var cnt = 0
      val loopCondAction = BasicStmtAction(loopStartEdges.first())
      loopVarValues.clear()
      while (!transFunc.getSuccStates(state, loopCondAction, prec).first().isBottom) {
        if (substituteLoopVar) loopVarValues.add(state.eval(loopVar).orElseThrow())
        cnt++
        if (UNROLL_LIMIT in 0 until cnt) return null
        state = transFunc.getSuccStates(state, BasicStmtAction(loopVarModifiers), prec).first()
      }
      return cnt
    }

    /**
     * A loop is a busy wait if it does not modify global state (global variables or heap memory)
     * and the values of local variables are the same for any positive number of executing the
     * loop.
     *
     * That is, we must check the following:
     * - No write access on global variables and dereferences
     * - Written local variables only transitively depend on variables/memory not modified in the
     *   loop
     */
    private val isBusyWait: Boolean by lazy {
      if (!collapseBusyWaits) return@lazy false
      // A dependency associate read variables to a written one with the following:
      // - global variables/memory are omitted (we can return right away when written)
      // - the map index is the written local variable
      // - the associated value is the set of values it depends on
      // A set of non-input variables is also maintained: a non-input is a local variable
      // that is already written in the loop.
      val waitlist = mutableMapOf(loopStart to BusyWaitState())
      val visited = mutableSetOf<XcfaLocation>()

      while (waitlist.isNotEmpty()) {
        val visiting = waitlist.keys.find { l ->
          l == loopStart || l.incomingEdges.all { it.source in loopLocs && it.source in visited }
        } ?: return@lazy false
        visited.add(visiting)
        val (dependencies, nonInputs, toggledMutexes) = waitlist.remove(visiting)!!
        visiting.outgoingEdges.forEach { edge ->
          if (edge.target in visited && edge.target != loopStart) {
            // nested loop, data flow is tricky
            return@lazy false
          }
          val d = dependencies.toMutableMap()
          val ni = nonInputs.toMutableSet()
          val tm = toggledMutexes.toMutableMap()
          edge.getFlatLabels().forEach { label ->
            if (label is InvokeLabel || label is ReturnLabel ||
                label is StartLabel || label is JoinLabel ||
                !update(d, ni, tm, label)) {
              return@lazy false
            }
          }
          if (edge.target in loopLocs && edge.target != loopStart) {
            val target = waitlist[edge.target]
            val newTarget = BusyWaitState(d, ni, tm)
            waitlist[edge.target] =
              if (target == null) newTarget
              else merge(target, newTarget) ?: return@lazy false
          }
        }
      }

      // A local written in the loop must not be live at the loop start: otherwise a later
      // iteration (or the code after the loop) can observe what an earlier iteration wrote, e.g.
      // through a guard or because the exit path does not overwrite it.
      val writtenLocals =
        loopEdges
          .flatMap { it.label.collectVarsWithAccessType().filter { a -> a.value.isWritten }.keys }
          .filter { it !in globalVars }
      writtenLocals.none { it in liveAtLoopStart }
    }

    /** Locals live at [loopStart] in the whole procedure (back edge and loop exits included). */
    var liveAtLoopStart: Set<VarDecl<*>> = emptySet()

    /**
     * A "state" of the busy wait check loop exploration.
     *
     * @param dependencies the index var depends on the associated set of "input" local vars
     * @param nonInputs the local vars that should not be treated as inputs (as they are written)
     * @param toggledMutexes changed mutexes in the loop (0: unchanged, -1: unlocked, 1: locked)
     */
    private data class BusyWaitState(
      val dependencies: Map<VarDecl<*>, Set<VarDecl<*>>> = emptyMap(),
      val nonInputs: Set<VarDecl<*>> = emptySet(),
      val toggledMutexes: Map<Expr<*>, Int> = emptyMap(),
    )

    private fun update(
      dependencies: MutableMap<VarDecl<*>, Set<VarDecl<*>>>,
      nonInputs: MutableSet<VarDecl<*>>,
      toggledMutexes: MutableMap<Expr<*>, Int>,
      label: XcfaLabel,
    ): Boolean {
      if (label.dereferencesWithAccessType.any { it.value.isWritten }) {
        // heap memory is written -> not a busy wait
        return false
      }

      if (label is FenceLabel) {
        label.acquiredMutexes.forEach { m ->
          toggledMutexes[m.lock] = toggledMutexes.getOrDefault(m.lock, 0) + 1
        }
        label.releasedMutexes.forEach { m ->
          toggledMutexes[m.lock] = toggledMutexes.getOrDefault(m.lock, 0) - 1
        }
      }

      val accesses = label.collectVarsWithAccessType()
      val writes = accesses.mapNotNull {
        if (it.value.isWritten) {
          if (it.key in globalVars) {
            // a global variable is written -> not a busy wait
            return false
          }
          it.key
        } else null
      }
      var reads = accesses.mapNotNull { if (it.value.isRead) it.key else null }.toSet()
      reads = reads.flatMap {
        when (it) {
          in nonInputs -> dependencies[it]!!
          in globalVars -> listOf()
          else -> listOf(it)
        }
      }.toSet()

      writes.forEach { w ->
        dependencies[w] = reads
        if (dependencies.any { w in it.value }) {
          // a written (local) variable is read in the loop -> not a busy wait
          return false
        }
        nonInputs.add(w)
      }

      return true
    }

    private fun merge(target1: BusyWaitState, target2: BusyWaitState): BusyWaitState? {
      val (d1, ni1, tm1) = target1
      val (d2, ni2, tm2) = target2
      if (tm1 != tm2) return null
      return BusyWaitState(
        (d1.keys + d2.keys).associateWith { (d1[it] ?: setOf()) + (d2[it] ?: setOf()) },
        (ni1 intersect ni2),
        tm1,
      )
    }

    /** Replaces the loop variable with its constant value for iteration [index], when enabled. */
    private fun substituteLoopVarIn(label: XcfaLabel, index: Int): XcfaLabel {
      if (!substituteLoopVar || parseContext == null || loopVar == null) return label
      val valuation = MutableValuation()
      valuation.put(loopVar, loopVarValues[index])
      return label.simplify(valuation, parseContext)
    }

    private fun copyBody(
      builder: XcfaProcedureBuilder,
      startLoc: XcfaLocation,
      index: Int,
      removeCond: Boolean,
    ): XcfaLocation {
      // `${name}_loop${index}` is not unique: copying the same region again in a later round
      // (nested loops produce exactly the clashing `_loop0_loop1` shapes) can regenerate a name the
      // procedure already holds. `addLoc` is a silent no-op for a location it already has, while
      // the map below would keep handing out the *stray* instance created here. XcfaLocation is a
      // data class, so edges built from that twin still satisfy addEdge's `in locs` check by
      // equality -- yet the twin owns its own, empty adjacency sets. Every adjacency-walking
      // traversal is then blind to those edges (including this pass's own back-edge cut), while
      // XcfaProcedure.deepCopy resolves endpoints through a map keyed by equality and re-points
      // them onto the registered instance. A cycle hidden that way only materialises in the
      // per-thread copy, where the OC checker rejects the task for "loops". Only disambiguate on an
      // actual clash, so the usual names stay stable.
      val takenNames = builder.getLocs().mapTo(mutableSetOf()) { it.name }
      val locs =
        loopLocs.associateWith {
          var name = "${it.name}_loop${index}"
          while (!takenNames.add(name)) name =
            "${it.name}_loop${index}_${XcfaLocation.uniqueCounter()}"
          val loc = XcfaLocation(name, metadata = it.metadata)
          builder.addLoc(loc)
          tracker.copied(loc, it)
          loc
        }

      loopEdges.forEach {
        val newSource = if (it.source == loopStart) startLoc else locs[it.source]!!
        val condStripped =
          if (it.source == loopCondStart && removeCond) it.label.removeCondition() else it.label
        val newLabel = substituteLoopVarIn(condStripped, index)
        val edge = XcfaEdge(newSource, locs[it.target]!!, newLabel, it.metadata)
        builder.addEdge(edge)
      }

      exitEdges.forEach { (loc, edges) ->
        for (edge in edges) {
          if (removeCond && loc == loopCondStart) continue
          val source = if (loc == loopStart) startLoc else locs[loc]!!
          builder.addEdge(XcfaEdge(source, edge.target, edge.label, edge.metadata))
        }
      }

      return locs[loopStart]!!
    }

    private fun XcfaLabel.removeCondition(): XcfaLabel {
      val stmtToRemove =
        getFlatLabels().find {
          it is StmtLabel && it.stmt is AssumeStmt && (it.collectVars() - loopVar).isEmpty()
        }
      return when {
        this == stmtToRemove -> NopLabel
        this is SequenceLabel -> SequenceLabel(labels.map { it.removeCondition() }, metadata)
        else -> this
      }
    }
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    globalVars = builder.parent.getVars().mapTo(mutableSetOf()) { it.wrappedVar }
    runUnroll(builder)
    // force unrolling leaves behind copies past the bound that nothing can reach
    return unusedLocRemovalPass.runChecked(builder)
  }

  private fun runUnroll(builder: XcfaProcedureBuilder) {
    // Before the loops: a spliced-in body brings its own loops with it, and those still have to be
    // taken apart by the search below.
    if (recursionUnrollLimit != -1) unrollRecursiveCalls(builder)

    // First, try to unroll without forcing (even if force unroll is allowed)
    if (forceUnrollLimit != -1) {
      var arbitraryLoop: Loop? = null
      while (true) {
        val loop = findLoop(builder) ?: break
        if (arbitraryLoop == null) arbitraryLoop = loop
        if (loop.unroll(builder, -1)) {
          arbitraryLoop = null
        }
        testedLoops.add(loop)
      }

      // Spare one loop finding iteration
      if (arbitraryLoop == null) {
        // Exit if there is no loops at all
        cutRemainingBackEdges(builder)
        return
      }
      arbitraryLoop.unroll(builder)
    }

    while (true) {
      val loop = findLoop(builder) ?: break
      loop.unroll(builder)
      testedLoops.add(loop)
    }

    if (forceUnrollLimit != -1) {
      cutRemainingBackEdges(builder)
    }
  }

  /**
   * Expands the calls left over after inlining, capping recursive ones at [recursionUnrollLimit].
   *
   * [InlineProceduresPass] refuses a procedure that (transitively) reaches recursion, and it
   * refuses it *whole*: `canInline` is all-or-nothing, so a single recursive callee leaves every
   * call in that procedure un-inlined, not just the recursive one. Backends that need a call-free
   * CFA (the OC checker does) then reject the task outright. Expanding here recovers those programs
   * whenever the interesting depth is bounded -- and, because this runs per force-unroll bound
   * rather than once at inlining time, raising the bound genuinely re-expands the recursion deeper.
   *
   * A call that is still recursive at the bound is cut, dropping the executions past it, which is
   * the same promise force unrolling makes for loops; [XcfaProcedureBuilder.setUnsafeUnroll]
   * records that so a `safe` verdict stays flagged as bound-limited.
   */
  private fun unrollRecursiveCalls(builder: XcfaProcedureBuilder) {
    val parseContext = parseContext ?: return
    // Counted per callee: a non-recursive call chain is finite and expands to nothing on its own,
    // so only the calls that can come back round need a cap.
    val recursive =
      recursiveProcedures
        ?: recursiveProcedureNames(builder.parent).also { recursiveProcedures = it }
    val expansions = mutableMapOf<String, Int>()
    while (true) {
      // Capture every body before anything in this round is spliced. A self-recursive call has the
      // callee and the caller as the same builder, so snapshotting after the call edge was removed
      // would splice a body with the recursive call already gone -- truncating the recursion to one
      // level, and doing so silently, with no cut and therefore no unsafe-unroll mark.
      val bodies = builder.parent.getProcedures().associate { it.name to it.snapshotBody() }
      var expandedOne = false
      for (edge in ArrayList(builder.getEdges())) {
        val pred: (XcfaLabel) -> Boolean = { builder.callsKnownProcedure(it) }
        val split = edge.splitIf(pred)
        if (split.isEmpty()) continue
        val hasCall = split.size > 1 || pred((split[0].label as SequenceLabel).labels[0])
        if (!hasCall) continue

        builder.removeEdge(edge)
        split.forEach { e ->
          val head = (e.label as SequenceLabel).labels[0]
          if (!pred(head)) {
            builder.addEdge(e)
            return@forEach
          }
          val invokeLabel = head as InvokeLabel
          val callee = checkNotNull(builder.calleeOf(invokeLabel))
          val bounded = callee.name in recursive
          val used = expansions.getOrDefault(callee.name, 0)
          val key = UnrollCut.RECURSION.key(builder.name, callee.name)
          if (bounded && used >= tracker.bound(key, recursionUnrollLimit)) {
            // Past the bound: drop the path rather than expand it again.
            builder.setUnsafeUnroll()
            tracker.cut(builder, key, e.source, listOf(SequenceLabel(listOf())), e.metadata)
            return@forEach
          }
          expansions[callee.name] = used + 1
          expandedOne = true
          inlineCallSite(
            builder = builder,
            source = e.source,
            target = e.target,
            invokeLabel = invokeLabel,
            callee = checkNotNull(bodies[callee.name]),
            parseContext = parseContext,
            freshFrame = true,
            metadata = e.metadata,
            onCopy = tracker::copied,
          )
        }
      }
      if (!expandedOne) return
    }
  }

  /**
   * Cuts any back edge [findLoop] left behind, once no more loops can be taken apart.
   *
   * A loop survives the pass whenever [getLoop] cannot describe it -- a shape whose elements
   * [getLoopElements] fails to determine, or one already attempted and recorded in [testedLoops] --
   * and the pass would then quietly return a CFA that still has cycles in it. That is harmless for
   * a backend that handles loops itself, but not for one that requires an acyclic CFA (the OC
   * checker rejects the whole task), so it is only done when a force-unroll bound is in effect:
   * that bound already limits the result to executions within it, and dropping a back edge keeps
   * exactly those, which is the same promise force unrolling makes everywhere else. The result is
   * marked unsafe-unroll accordingly, so a `safe` verdict stays flagged as bound-limited.
   */
  private fun cutRemainingBackEdges(builder: XcfaProcedureBuilder) {
    while (true) {
      val backEdge = findBackEdge(builder.initLoc) ?: break
      builder.setUnsafeUnroll()
      builder.removeEdge(backEdge)
      val key = tracker.key(UnrollCut.BACK_EDGE, builder, backEdge.target)
      tracker.cut(builder, key, backEdge.source, listOf(backEdge.label), backEdge.metadata)
    }
  }

  /**
   * Any edge that closes a cycle reachable from [initLoc], or null when the CFA is acyclic.
   *
   * Standard three-colour DFS: an edge is a back edge exactly when its target is still on the
   * recursion stack. Marking edges explored globally instead would miss cycles -- a back edge first
   * reached along a path that does not go through its target is then never recognised as one, and
   * the surviving cycle only shows up much later as the OC checker rejecting the task for "loops".
   */
  private fun findBackEdge(initLoc: XcfaLocation): XcfaEdge? { // DFS
    val onStack = mutableSetOf<XcfaLocation>()
    val finished = mutableSetOf<XcfaLocation>()
    val stack = mutableListOf<Pair<XcfaLocation, Iterator<XcfaEdge>>>()

    fun push(loc: XcfaLocation) {
      onStack.add(loc)
      stack.add(loc to loc.outgoingEdges.toList().iterator())
    }

    push(initLoc)
    while (stack.isNotEmpty()) {
      val (loc, edges) = stack.last()
      if (edges.hasNext()) {
        val edge = edges.next()
        if (edge.target in onStack) return edge
        if (edge.target !in finished) push(edge.target)
      } else {
        stack.removeLast()
        onStack.remove(loc)
        finished.add(loc)
      }
    }
    return null
  }

  private fun findLoop(builder: XcfaProcedureBuilder): Loop? { // DFS
    val stack = Stack<XcfaLocation>()
    val explored = mutableSetOf<XcfaEdge>()
    stack.push(builder.initLoc)
    while (stack.isNotEmpty()) {
      val current = stack.peek()
      val edgesToExplore = current.outgoingEdges subtract explored
      if (edgesToExplore.isEmpty()) {
        stack.pop()
      } else {
        val edge = edgesToExplore.elementAt(random.nextInt(edgesToExplore.size))
        if (edge.target in stack) { // loop found
          getLoop(builder, edge)?.let {
            return it
          }
        } else {
          stack.push(edge.target)
        }
        explored.add(edge)
      }
    }
    return null
  }

  /** Find a loop from the given start location that can be unrolled. */
  private fun getLoop(builder: XcfaProcedureBuilder, backEdge: XcfaEdge): Loop? {
    val loopStart = backEdge.target
    var properlyUnrollable = true
    var loopCondStart = loopStart
    while (
      loopCondStart.outgoingEdges.size == 1 &&
        loopCondStart.outgoingEdges.first().let {
          it.label.getFlatLabels().isEmpty() && it.target != loopStart
        }
    ) {
      loopCondStart = loopCondStart.outgoingEdges.first().target
    }
    // loopCondStart is the first loop location with a non-empty outgoing edge
    if (loopCondStart.outgoingEdges.size != 2) {
      properlyUnrollable = false // more than two outgoing edges from the loop start not supported
    }

    val (loopLocations, loopEdges) = getLoopElements(backEdge)
    if (loopEdges.isEmpty()) return null // unsupported loop structure

    val loopCondEdges = loopCondStart.outgoingEdges.filter { it.target in loopLocations }
    if (loopCondEdges.size != 1)
      properlyUnrollable = false // more than one loop condition not supported

    // find the loop variable based on the outgoing edges from the loop start location
    val loopVar =
      loopCondStart.outgoingEdges
        .map {
          val vars = it.label.collectVarsWithAccessType()
          if (vars.size != 1) {
            null // multiple variables in the loop condition not supported
          } else {
            vars.keys.first()
          }
        }
        // reduceOrNull, not reduce: a loop-condition location with no outgoing edges at all (a dead
        // end left behind by an earlier unroll) makes this an empty collection, and `reduce` throws
        // "Empty collection can't be reduced" instead of just reporting that no single loop
        // variable
        // could be identified. Null is already the "not properly unrollable" answer handled below.
        .reduceOrNull { v1, v2 -> if (v1 != v2) null else v1 }
    if (loopVar == null) properlyUnrollable = false

    val (loopVarInit, loopVarModifiers) =
      run {
        if (!properlyUnrollable) return@run null

        // find (a subset of) edges that are executed in every loop iteration
        var edge = loopCondStart.outgoingEdges.find { it.target in loopLocations }!!
        val necessaryLoopEdges = mutableListOf(edge)
        while (edge.target.outgoingEdges.size == 1) {
          edge = edge.target.outgoingEdges.first()
          necessaryLoopEdges.add(edge)
        }
        val finalEdges = loopStart.incomingEdges.filter { it.source in loopLocations }
        if (finalEdges.size == 1) {
          edge = finalEdges.first()
          val finalPath = mutableListOf(edge)
          while (edge.source.incomingEdges.size == 1) {
            edge = edge.source.incomingEdges.first()
            finalPath.add(edge)
          }
          necessaryLoopEdges.addAll(finalPath.reversed().filter { it !in necessaryLoopEdges })
        }

        // find edges that modify the loop variable
        val loopVarModifiers =
          loopEdges.filter {
            val vars = it.label.collectVarsWithAccessType()
            if (vars[loopVar].isWritten) {
              if (it !in necessaryLoopEdges || vars.size > 1)
                return@run null // loop variable modification cannot be determined statically
              true
            } else {
              false
            }
          }

        // find loop variable initialization before the loop
        lateinit var loopVarInit: XcfaEdge
        var loc = loopStart
        while (true) {
          val inEdges = loc.incomingEdges.filter { it.source !in loopLocations }
          if (inEdges.size != 1) return@run null
          val inEdge = inEdges.first()
          val vars = inEdge.label.collectVarsWithAccessType()
          if (vars[loopVar].isWritten) {
            if (vars.size > 1) return@run null
            loopVarInit = inEdge
            break
          }
          loc = inEdge.source
        }

        loopVarInit to loopVarModifiers.sortedBy(necessaryLoopEdges::indexOf)
      }
        ?: run {
          properlyUnrollable = false
          null to null
        }

    val exits =
      loopLocations
        .mapNotNull { loc ->
          val exitEdges = loc.outgoingEdges.filter { it.target !in loopLocations }
          if (exitEdges.isEmpty()) null else (loc to exitEdges)
        }
        .toMap()
    val exitKey = tracker.key(UnrollCut.LOOP, builder, loopStart)
    return Loop(
        loopStart = loopStart,
        loopCondStart = loopCondStart,
        loopLocs = loopLocations,
        loopEdges = loopEdges,
        loopVar = loopVar,
        loopVarInit = loopVarInit,
        loopVarModifiers = loopVarModifiers,
        loopStartEdges = loopCondEdges,
        exitEdges = exits,
        properlyUnrollable = properlyUnrollable,
        forceUnrollLimit = tracker.bound(exitKey, forceUnrollLimit),
        // Never for a global loop variable: another thread could write it, so its per-iteration
        // value is not a constant of the copy, and baking one in would hide a race or a
        // memory-safety violation on whatever the loop indexes.
        substituteLoopVar =
          substituteLoopVar && builder.parent.getVars().none { it.wrappedVar == loopVar },
        parseContext = parseContext,
        exitKey = exitKey,
        tracker = tracker,
        collapseBusyWaits = collapseBusyWaits,
        globalVars = globalVars,
      )
      .also { if (it in testedLoops) return null }
      .also { it.liveAtLoopStart = strongLiveVars(builder)[loopStart] ?: emptySet() }
  }
}
