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
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.simplify
import java.util.*
import kotlin.math.max

/**
 * Unrolls loops where the number of loop executions can be determined statically. The UNROLL_LIMIT
 * refers to the number of loop executions: loops that are executed more times than this limit are
 * not unrolled. Loops with unknown number of iterations are unrolled to FORCE_UNROLL_LIMIT
 * iterations (this way a safe result might not be valid).
 */
/**
 * @param substituteLoopVar when true, each unrolled copy has the loop variable replaced by its
 *   constant value for that iteration (`&t[i]` becomes `&t[0]`, `&t[1]`, …). Only the loop variable
 *   is substituted, so address-of expressions of other variables (`&x`) are left for
 *   ReferenceElimination -- which is why this may safely run before it. Requires [parseContext].
 */
class LoopUnrollPass(
  alwaysForceUnroll: Int = -1,
  private val substituteLoopVar: Boolean = false,
  private val parseContext: ParseContext? = null,
  unrollRecursion: Boolean? = null,
) : ProcedurePass {

  companion object {

    var UNROLL_LIMIT = 1000
    var FORCE_UNROLL_LIMIT = -1

    /**
     * Expand recursive calls to the force-unroll bound, the same way loops are expanded to it.
     *
     * This lives here rather than in [InlineProceduresPass] on purpose. Inlining runs once, up
     * front, and gives up entirely on a procedure that (transitively) reaches recursion --
     * `canInline` is all-or-nothing, so one recursive callee leaves *every* call in that procedure
     * un-inlined. A backend that raises its bound and re-runs (the OC checker escalates
     * `forceUnrollBound` until a safe result is no longer bound-limited) therefore gets no benefit
     * from it. Expanding here means each new bound re-expands the recursion to the new depth, and
     * the result is marked unsafe-unroll exactly like a force-unrolled loop, so a `safe` verdict
     * stays flagged as bound-limited.
     *
     * On by default: it only ever fires where a force-unroll bound is already in effect, and a
     * program without recursion has nothing for it to expand, so the programs it changes are
     * exactly the ones a call-free-CFA backend used to reject outright.
     */
    var UNROLL_RECURSION = true

    /**
     * Seed for the order [findLoop] explores edges in.
     *
     * Which loop the search happens to reach first decides which loops get taken apart and which
     * are left for the fallbacks, so an unseeded source made the whole pass -- and every verdict
     * downstream of it -- differ between two runs of the same input. That turns a reproducible
     * failure into an intermittent one; set this to vary the exploration deliberately instead.
     */
    var EXPLORATION_SEED = 0L

    private val transFunc: ExplStmtTransFunc by lazy {
      val solver = Z3SolverFactory.getInstance().createSolver()
      ExplStmtTransFunc.create(solver, 1)
    }
  }

  private val forceUnrollLimit = max(FORCE_UNROLL_LIMIT, alwaysForceUnroll)

  private val unrollRecursion = unrollRecursion ?: UNROLL_RECURSION

  /** Seeded so that the same input explores loops the same way on every run. */
  private val exploration = java.util.Random(EXPLORATION_SEED)

  private val testedLoops = mutableSetOf<Loop>()

  /**
   * Which procedures are recursive, decided once for the whole program.
   *
   * The pass instance is reused across procedures, and expanding a call rewrites the *callee's*
   * body in place, so asking again once some bodies have already been expanded gives a different --
   * and order-dependent -- answer. Recursion is a property of the program as it arrived, so it is
   * settled on first use and kept.
   */
  private var recursiveProcedures: Set<String>? = null

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
  ) {

    /** The loop variable's value at each iteration, filled by [count] when [substituteLoopVar]. */
    private val loopVarValues = mutableListOf<LitExpr<*>>()

    private class BasicStmtAction(private val stmt: Stmt) : StmtAction() {
      constructor(edge: XcfaEdge) : this(edge.label.toStmt())

      constructor(edges: List<XcfaEdge>) : this(SequenceLabel(edges.map { it.label }).toStmt())

      override fun getStmts() = listOf(stmt)
    }

    fun unroll(builder: XcfaProcedureBuilder) {
      val c = count()
      if (c != null) {
        unroll(builder, c, true)
      } else if (forceUnrollLimit != -1) {
        builder.setUnsafeUnroll()
        unroll(builder, forceUnrollLimit, false)
      }
    }

    fun unroll(builder: XcfaProcedureBuilder, count: Int, removeCond: Boolean) {
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
    }

    private fun count(): Int? {
      if (!properlyUnrollable) return null
      check(loopVar != null && loopVarModifiers != null && loopVarInit != null)
      check(loopStartEdges.size == 1)

      // Counting the iterations means asking a solver to evaluate these statements, and the
      // dereferences the frontend emits carry no `uniquenessIdx` -- which every solver transformer
      // rejects outright ("Incomplete dereferences ... are not handled properly"). That index is
      // added later, and only on the CEGAR path (`PtrUtils.uniqueDereferences`, driven by
      // `PtrAction`), so a pass running before it must not hand a dereference to the solver at all.
      // A loop whose trip count touches memory therefore counts as "not statically known", exactly
      // like any other loop this analysis cannot resolve: return null and let the caller force
      // unroll it. Without this the pass throws, which killed every OC run on a task with such a
      // loop.
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
    // Before the loops: a spliced-in body brings its own loops with it, and those still have to be
    // taken apart by the search below.
    if (forceUnrollLimit != -1 && unrollRecursion) unrollRecursiveCalls(builder)
    while (true) {
      val loop = findLoop(builder.initLoc) ?: break
      loop.unroll(builder)
      testedLoops.add(loop)
    }
    if (forceUnrollLimit != -1) cutRemainingBackEdges(builder)
    return builder
  }

  /**
   * Expands the calls left over after inlining, capping recursive ones at [forceUnrollLimit].
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
          if (bounded && used >= forceUnrollLimit) {
            // Past the bound: drop the path rather than expand it again.
            builder.setUnsafeUnroll()
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

  private fun findLoop(initLoc: XcfaLocation): Loop? { // DFS
    val stack = Stack<XcfaLocation>()
    val explored = mutableSetOf<XcfaEdge>()
    stack.push(initLoc)
    while (stack.isNotEmpty()) {
      val current = stack.peek()
      val edgesToExplore = current.outgoingEdges subtract explored
      if (edgesToExplore.isEmpty()) {
        stack.pop()
      } else {
        // Deterministic given EXPLORATION_SEED: `edgesToExplore` keeps insertion order (the sets
        // it comes from are linked), so indexing it with a seeded source repeats exactly.
        val edge = edgesToExplore.elementAt(exploration.nextInt(edgesToExplore.size))
        if (edge.target in stack) { // loop found
          getLoop(edge)?.let {
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
  private fun getLoop(backEdge: XcfaEdge): Loop? {
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
        val necessaryLoopEdges = mutableSetOf(edge)
        while (edge.target.outgoingEdges.size == 1) {
          edge = edge.target.outgoingEdges.first()
          necessaryLoopEdges.add(edge)
        }
        val finalEdges = loopStart.incomingEdges.filter { it.source in loopLocations }
        if (finalEdges.size == 1) {
          edge = finalEdges.first()
          necessaryLoopEdges.add(edge)
          while (edge.source.incomingEdges.size == 1) {
            edge = edge.source.incomingEdges.first()
            necessaryLoopEdges.add(edge)
          }
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

        loopVarInit to loopVarModifiers
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
        forceUnrollLimit = forceUnrollLimit,
        substituteLoopVar = substituteLoopVar,
        parseContext = parseContext,
      )
      .also { if (it in testedLoops) return null }
  }
}
