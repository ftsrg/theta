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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.simplify
import java.util.*

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
 */
class UnrollPass(
  specificForceUnrollLimit: Int? = null,
  specificRecursionUnrollLimit: Int? = null,
  private val substituteLoopVar: Boolean = false,
  private val parseContext: ParseContext? = null,
  private val busyWaitsOnly: Boolean = false,
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
     * Off by default: it is exact for reachability but not for termination (see [Loop.isBusyWait]),
     * and a program without a waiting loop has nothing for it to change.
     */
    var COLLAPSE_BUSY_WAITS = false

    /**
     * Seed for the order [findLoop] explores edges in.
     *
     * Which loop the search happens to reach first decides which loops get taken apart and which
     * are left for the fallbacks, so an unseeded source made the whole pass -- and every verdict
     * downstream of it -- differ between two runs of the same input. That turns a reproducible
     * failure into an intermittent one; set this to vary the exploration deliberately instead.
     */
    var EXPLORATION_SEED = 0L

    /**
     * The variables this label reads and the ones it writes, kept apart.
     *
     * Not [collectVarsWithAccessType]: that one builds an assignment's map as "every variable of
     * the right-hand side reads" `+` "the target writes", and the `+` on maps *replaces* the entry
     * for a variable that appears on both sides. `i = i + 1` therefore comes back as a write of `i`
     * and no read of it, which is exactly the dependency [isBusyWait] has to see.
     */
    private fun XcfaLabel.readsAndWrites(): Pair<Set<VarDecl<*>>, Set<VarDecl<*>>> =
      when {
        this is StmtLabel && stmt is AssignStmt<*> ->
          ExprUtils.getVars(stmt.expr) to setOf(stmt.varDecl)
        this is StmtLabel && stmt is HavocStmt<*> ->
          emptySet<VarDecl<*>>() to setOf(stmt.varDecl)
        this is StmtLabel -> StmtUtils.getVars(stmt) to emptySet()
        else -> emptySet<VarDecl<*>>() to emptySet()
      }

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

  /** Seeded so that the same input explores loops the same way on every run. */
  private val exploration = java.util.Random(EXPLORATION_SEED)

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
        unroll(builder, c, true)
        return true
      } else if (forceLimit != -1) {
        builder.setUnsafeUnroll()
        unroll(builder, forceLimit, false)
        return true
      }
      return false
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

    /**
     * Whether [unroll] should replace this loop with a single iteration of itself: the loop can
     * only wait, so nothing it does is visible outside the thread and no iteration changes what
     * another iteration reads.
     *
     * `while (vatomic32_read(&a) != c) {}` -- the shape every libvsync lock spins on -- can only
     * leave the loop because *another* thread wrote the location it polls. Its iterations differ in
     * nothing but the value read, so the whole loop is equivalent to a single iteration that reads
     * the value it was waiting for. Any execution that spins k times maps onto one that spins once:
     * the discarded iterations are invisible to the other threads, so deleting them from the
     * interleaving leaves a run that is still possible and ends in the same state. What the
     * collapse does drop is the run that spins forever, which makes it exact for reachability but
     * not for termination.
     *
     * Three conditions make that deletion legitimate, one per way it could go wrong, and each is
     * one standard analysis over the loop:
     * - **Nothing carried in.** No variable the loop writes may be read before it is written, on
     *   any path through an iteration ([carriedInVars]). Otherwise the kept iteration, which starts
     *   from the state before the loop rather than from the state a deleted iteration left, reads
     *   something that is no longer there.
     * - **Nothing observable.** No call, thread start or join, mutex operation or havoc, and a
     *   write to a global or through a dereference only when its value and its address are the same
     *   in every iteration ([invariantVars], [repeatsHarmlessly]) -- writing what is already there
     *   is not a state change, which is what lets a spinlock's `xchg` retry through. Otherwise a
     *   deleted iteration is one another thread could have seen.
     * - **Nothing carried out.** Whatever the loop writes and something after it still reads has to
     *   be written on every path to each way out ([mustWrittenPerLoc], against [liveOut]).
     *   Otherwise the kept iteration leaves a variable holding its pre-loop value where the real
     *   run has a deleted iteration's write in it.
     *
     * The first is asked first: with nothing carried in, everything an iteration computes is a
     * function of the state before the loop and of what it read from the environment as it ran,
     * which is what makes "the same in every iteration" a meaningful thing for the second to
     * decide. Everything else the kept iteration needs it gets for free from *where* it is
     * scheduled -- deleting the earlier iterations leaves it in the position the last one held, so
     * it reads what that one read and takes the branches that one took.
     *
     * [liveOut] says, per location, which variables anything after it still reads, which is what
     * decides whether one of the loop's writes is visible outside it at all.
     */
    fun collapsible(liveOut: Map<XcfaLocation, Set<VarDecl<*>>>) =
      collapseBusyWaits && isBusyWait(liveOut)

    private fun isBusyWait(liveOut: Map<XcfaLocation, Set<VarDecl<*>>>): Boolean {
      val exits = exitEdges.flatMap { (loc, edges) -> edges.map { loc to it } }
      if (exits.isEmpty()) return false // a loop with no way out is not waiting for anything

      val written = loopEdges.flatMapTo(mutableSetOf()) { it.writtenVars() }

      // Nothing carried in, and asked first: it is what makes "the same in every iteration" mean
      // anything to the second condition.
      if (carriedInVars(written).isNotEmpty()) return false

      // Nothing another thread can tell happened.
      val invariant = invariantVars()
      if (loopEdges.flatMap { it.getFlatLabels() }.any { !it.repeatsHarmlessly(invariant) })
        return false

      // Nothing carried out, at each way out of the loop. Leaving from the start is not one of
      // them: the previous iteration has just finished there, which is what the back edges stand
      // for, and the path from the start to the test carries no statement at all.
      val mustWritten = mustWrittenPerLoc(written)
      val ends =
        loopStart.incomingEdges.filter { it.source in loopLocs } +
          exits.filterNot { it.first == loopStart || it.first == loopCondStart }.map { it.second }
      // Only what is still live there, and libvsync's waiting loops are full of writes that are
      // not: the empty `verification_spin_end` hook and the await helper's own return value both
      // leave a temporary assigned on one branch of the loop and read by nobody.
      return ends.all { edge ->
        val done = (mustWritten[edge.source] ?: emptySet()) + edge.writtenVars()
        (written intersect (liveOut[edge.target] ?: emptySet())).all { it in done }
      }
    }

    /**
     * For each loop location, the variables written on *every* intra-loop path that reaches it from
     * [loopStart] -- i.e. what an iteration has certainly written by the time it gets there.
     *
     * A must-analysis, so it starts from everything and shrinks: [loopStart] holds the empty set
     * because that is where an iteration begins, which is also what stops the fixpoint from
     * carrying one iteration's writes into the next.
     */
    private fun mustWrittenPerLoc(written: Set<VarDecl<*>>): Map<XcfaLocation, Set<VarDecl<*>>> {
      val result =
        loopLocs.associateWithTo(mutableMapOf()) { if (it == loopStart) emptySet() else written }
      while (true) {
        var changed = false
        for (loc in loopLocs) {
          if (loc == loopStart) continue
          val inEdges = loc.incomingEdges.filter { it.source in loopLocs }
          if (inEdges.isEmpty()) continue
          val next =
            inEdges
              .map { (result[it.source] ?: emptySet()) + it.writtenVars() }
              .reduce { a, b -> a intersect b }
          if (next != result[loc]) {
            result[loc] = next
            changed = true
          }
        }
        if (!changed) return result
      }
    }

    private fun XcfaEdge.readVars(): Set<VarDecl<*>> =
      getFlatLabels().flatMapTo(mutableSetOf()) { it.readsAndWrites().first }

    private fun XcfaEdge.writtenVars(): Set<VarDecl<*>> =
      label.collectVarsWithAccessType().filterValues { it.isWritten }.keys

    /**
     * The variables an iteration takes a value from an earlier iteration of: those the loop writes
     * and that some path through it reads before writing.
     *
     * A backward may-analysis over the loop. A back edge and a way out both end the iteration, so
     * both contribute only what their own labels read and nothing of what is read beyond them --
     * for a way out that is deliberate, since reproducing what the *rest of the procedure* reads is
     * the third condition's question, asked against liveness rather than against this.
     *
     * The question is asked of the *body*, not of the whole iteration, and the difference is the
     * loop's own test: `while (o != 1) { o = read(a); }` reads `o` before the body writes it, and
     * that read is answered by the body all the same, because the collapsed loop leaves through
     * that same test *after* the kept iteration has run. Only a read the body has not written
     * itself by the time it reaches it is stale.
     *
     * This is the position-sensitive half of the criterion, and nothing else in it can stand in for
     * that. Asking instead whether a value is computed from its own previous value -- a cycle in
     * the graph of "the value written to x reads y" -- is both too weak and too strong: it misses
     * `t = v` on a path that has not written `v` yet (no cycle, and `v` can still be written on
     * every path, so the must-analysis below is satisfied too, while `t` silently receives the
     * previous iteration's `v`), and it refuses `i = 0; ...; i = i + 1`, where the reset makes
     * every iteration start from the same value. Asking whether the read is *preceded by a write on
     * its own path* is exactly the question, and it is well defined on a cycle -- unlike an
     * order-based test over the whole loop, where rotating the cut turns an intra-iteration read
     * into a loop-carried one.
     */
    private fun carriedInVars(written: Set<VarDecl<*>>): Set<VarDecl<*>> {
      val exposed = loopLocs.associateWithTo(mutableMapOf()) { emptySet<VarDecl<*>>() }
      while (true) {
        var changed = false
        for (loc in loopLocs) {
          val next =
            loc.outgoingEdges.flatMapTo(mutableSetOf()) { edge ->
              var here =
                if (edge in loopEdges && edge.target != loopStart) exposed.getValue(edge.target)
                else emptySet()
              for (label in edge.getFlatLabels().reversed()) {
                val (reads, writes) = label.readsAndWrites()
                here = here - writes + reads
              }
              here
            }
          if (next != exposed[loc]) {
            exposed[loc] = next
            changed = true
          }
        }
        if (!changed) break
      }

      // The loop's own test is the one read the body does not have to answer: it is evaluated
      // again after the kept iteration -- that is where the collapsed loop leaves from -- so the
      // write the body makes is what satisfies it, which the third condition checks against
      // liveness at the head. Everything else on the edges into the body counts, so only the
      // leading assumes are skipped, never a statement LBE merged in behind them.
      val insideBody =
        loopCondStart.outgoingEdges
          .filter { it in loopEdges }
          .flatMapTo(mutableSetOf()) { edge ->
            var here =
              if (edge.target == loopStart) emptySet<VarDecl<*>>()
              else exposed.getValue(edge.target)
            val labels = edge.getFlatLabels()
            for (label in
              labels.dropWhile { it is StmtLabel && it.stmt is AssumeStmt }.reversed()) {
              val (reads, writes) = label.readsAndWrites()
              here = here - writes + reads
            }
            here
          }
      return written intersect insideBody
    }

    /**
     * The variables whose value at any one point in the loop is the same in every iteration.
     *
     * Once [carriedInVars] is empty, that is simply the variables no read of the environment
     * reaches: a value built from literals and from what the thread already held when it entered
     * the loop cannot differ between iterations, while one that came from a global, from memory or
     * from a havoc can. Read off the graph of "the value written to x reads y", with a mark on
     * every variable assigned something the thread does not own.
     */
    private fun invariantVars(): Set<VarDecl<*>> {
      val readFrom = mutableMapOf<VarDecl<*>, MutableSet<VarDecl<*>>>()
      val fromEnvironment = mutableSetOf<VarDecl<*>>()
      val mentioned = mutableSetOf<VarDecl<*>>()
      for (label in loopEdges.flatMap { it.getFlatLabels() }) {
        val (reads, writes) = label.readsAndWrites()
        mentioned.addAll(reads + writes)
        val owned =
          label is StmtLabel && label.stmt !is HavocStmt<*> && label.dereferences.isEmpty()
        for (target in writes) {
          readFrom.getOrPut(target) { mutableSetOf() }.addAll(reads)
          if (!owned) fromEnvironment.add(target)
        }
      }
      return mentioned.filterTo(mutableSetOf()) { v ->
        val seen = mutableSetOf(v)
        val toVisit = ArrayDeque(listOf(v))
        while (toVisit.isNotEmpty()) {
          for (u in readFrom[toVisit.removeFirst()] ?: emptySet()) if (seen.add(u)) toVisit.add(u)
        }
        seen.none { it in globalVars || it in fromEnvironment }
      }
    }

    /** Whether this expression's value is the same in every iteration. */
    private fun Expr<*>.isInvariant(invariant: Set<VarDecl<*>>) =
      ExprUtils.getVars(this).none { it !in invariant } && dereferences.isEmpty()

    /**
     * Whether running this label a second time, with the loop's state as it left it, changes
     * nothing.
     *
     * Rejecting every write outright was too crude, and it threw away the loop that matters most: a
     * spinlock's acquire is `while (xchg(&flag, 1) != 0) await_eq(&flag, 0);`, and every failed
     * attempt writes the same value to the same location. Writing what is already there is not a
     * state change, so those iterations are as repeatable as a pure read, and no other thread can
     * tell how many of them happened.
     *
     * So a write is allowed when both the value and the address are *invariant* -- the same in
     * every iteration, as [invariantVars] decides. Anything read through a dereference or from a
     * global is not, because then two iterations can write different things and dropping one of
     * them can hide a state another thread could have seen. Calls, thread starts and joins, mutex
     * operations and havocs stay out regardless.
     */
    private fun XcfaLabel.repeatsHarmlessly(invariant: Set<VarDecl<*>>): Boolean =
      when (this) {
        is StmtLabel ->
          when (val s = stmt) {
            is HavocStmt<*> -> false
            is MemoryAssignStmt<*, *, *> ->
              s.expr.isInvariant(invariant) && s.deref.isInvariant(invariant)
            is AssignStmt<*> -> s.varDecl !in globalVars || s.expr.isInvariant(invariant)
            else -> dereferencesWithAccessType.none { it.value.isWritten }
          }
        is AtomicFenceLabel -> true // an atomic block around the poll is fine, it is still a poll
        is NopLabel -> true
        else -> false // calls, thread start/join, mutexes, and anything else unexamined
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

    // Waiting loops first, and as a phase of their own: each collapse removes a cycle, and a loop
    // that cannot be collapsed is simply left to the unrolling below.
    while (true) {
      val loop = findCollapsibleLoop(builder) ?: break
      loop.unroll(builder, 1, false)
    }
    // The collapse leaves the entry to a second iteration unreachable, so the same removal the
    // force-unrolled copies need applies here too.
    if (busyWaitsOnly) return

    // First, try to unroll without forcing (even if force unroll is allowed)
    if (forceUnrollLimit != -1) {
      val loopStarts = mutableSetOf<XcfaLocation>()
      var arbitraryLoop: Loop? = null
      while (true) {
        val loop = findLoop(builder, loopStarts) ?: break
        if (arbitraryLoop == null) arbitraryLoop = loop
        if (loop.unroll(builder, -1)) {
          arbitraryLoop = null
          loopStarts.clear()
        } else {
          loopStarts.add(loop.loopStart)
        }
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
    if (forceUnrollLimit != -1) cutRemainingBackEdges(builder)
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
          if (bounded && used >= recursionUnrollLimit) {
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

  private fun findLoop(
    builder: XcfaProcedureBuilder,
    discoveredLoopStarts: Set<XcfaLocation> = setOf(),
  ): Loop? {
    // DFS
    val stack = Stack<XcfaLocation>()
    val explored = mutableSetOf<XcfaEdge>()
    stack.push(builder.initLoc)
    while (stack.isNotEmpty()) {
      val current = stack.peek()
      val edgesToExplore = current.outgoingEdges subtract explored
      if (edgesToExplore.isEmpty()) {
        stack.pop()
      } else {
        // Deterministic given EXPLORATION_SEED: `edgesToExplore` keeps insertion order (the sets
        // it comes from are linked), so indexing it with a seeded source repeats exactly.
        val edge = edgesToExplore.elementAt(exploration.nextInt(edgesToExplore.size))
        if (edge.target in stack && edge.target !in discoveredLoopStarts) { // loop found
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

  /**
   * A loop in the procedure that can be replaced by a single iteration of itself, or null.
   *
   * Every edge is tried as the cut, rather than whatever edge a walk of the CFA happens to close a
   * cycle on. Which edge of a cycle is called the back edge decides what one iteration *is*: cut a
   * waiting loop between its read and its test and one iteration no longer contains the read, so
   * [Loop.collapsible] insists on the cut being at the test. Worse, a waiting loop sits inside the
   * thread's outer loop, and a search for cycles reaches that one first -- with the inner cycle
   * never offered on its own, and its exit lying on the outer cycle, so that cutting there
   * describes the whole thread body. Trying every edge costs a reachability check per edge on a
   * procedure with a few hundred of them, and it does not depend on the search order at all.
   */
  private fun findCollapsibleLoop(builder: XcfaProcedureBuilder): Loop? {
    val liveOut = liveVars(builder) ?: return null
    return builder.getEdges().firstNotNullOfOrNull { edge ->
      loopCutAt(edge)?.takeIf { it.collapsible(liveOut) }
    }
  }

  /**
   * Whether this label is an assignment to a variable and nothing else, so that it does nothing at
   * all when its target is never used. Anything else -- an assume, a write through a dereference, a
   * call, a fence -- has to be treated as a use of what it reads.
   */
  private val XcfaLabel.isPlainAssignment
    get() = this is StmtLabel && stmt is AssignStmt<*>

  /**
   * Per location, the variables some path from it still *uses*: backward strong liveness over the
   * procedure.
   *
   * Needed because "can anything tell which iteration of the waiting loop wrote this variable" is a
   * question about liveness and nothing else -- and plain liveness is not enough for the loops in
   * libvsync. The await helper's return value is read exactly once, by the assignment that hands it
   * to a call temporary that nobody reads; ordinary liveness dutifully keeps it live for the sake
   * of that dead assignment. Strong liveness ignores the reads of an assignment whose target is
   * itself not strongly live, which collapses the whole dead chain in one pass. Anything that is
   * not a plain assignment -- an assume, a write to memory or to a global -- always counts as a
   * use.
   *
   * Null when the procedure can still be called, since then its final location's live set is
   * whatever the caller goes on to read, which is not visible from here. After inlining the
   * procedures that matter have no callers left.
   */
  private fun liveVars(builder: XcfaProcedureBuilder): Map<XcfaLocation, Set<VarDecl<*>>>? {
    val called =
      builder.parent.getProcedures().any { proc ->
        proc.getEdges().any { edge ->
          edge.getFlatLabels().any { it is InvokeLabel && it.name == builder.name }
        }
      }
    if (called) return null

    val live = builder.getLocs().associateWithTo(mutableMapOf()) { emptySet<VarDecl<*>>() }
    while (true) {
      var changed = false
      for (loc in builder.getLocs()) {
        val next =
          loc.outgoingEdges.flatMapTo(mutableSetOf()) { edge ->
            // Backwards through the edge, carrying the live set as it grows: a read before the
            // write on the same edge keeps the variable live, a write before it does not, and the
            // reads of an assignment nothing goes on to use do not count at all.
            var here = live[edge.target] ?: emptySet()
            for (label in edge.getFlatLabels().reversed()) {
              val (reads, writes) = label.readsAndWrites()
              val used = writes.isEmpty() || writes.any { it in here } || !label.isPlainAssignment
              here = here - writes
              if (used) here = here + reads
            }
            here
          }
        if (next != live[loc]) {
          live[loc] = next
          changed = true
        }
      }
      if (!changed) return live
    }
  }

  /**
   * The natural loop of [backEdge]: its target, plus everything that reaches its source without
   * passing that target. Null when there is no such loop.
   *
   * Same walk as [getLoopElements], with two differences that the collapse needs. It keeps only the
   * edges *between* the loop's locations, where [getLoopElements] also collects the edges that come
   * into those locations from outside and drops the one it takes for the loop's entry -- and
   * [Loop.unroll] replaces every outgoing edge of a loop location with the set it was given, so
   * either discrepancy corrupts the procedure. And it refuses the cut when the walk escapes to a
   * location without predecessors, which means the target does not dominate the source: the "loop"
   * of such an edge is not a loop at all. Cutting a waiting loop between its read and its test is
   * exactly that case, which is why every edge is worth trying.
   */
  private fun loopCutAt(backEdge: XcfaEdge): Loop? {
    val loopStart = backEdge.target
    val loopLocs = mutableSetOf(loopStart)
    val toVisit = ArrayDeque(listOf(backEdge.source))
    while (toVisit.isNotEmpty()) {
      val loc = toVisit.removeFirst()
      if (loc == loopStart) continue
      if (loc.incomingEdges.isEmpty()) return null // loopStart does not dominate the back edge
      if (loopLocs.add(loc)) toVisit.addAll(loc.incomingEdges.map { it.source })
    }
    val loopEdges =
      loopLocs.flatMapTo(mutableSetOf()) { loc ->
        loc.outgoingEdges.filter { it.target in loopLocs }
      }
    if (backEdge !in loopEdges) return null

    var loopCondStart = loopStart
    while (
      loopCondStart.outgoingEdges.size == 1 &&
        loopCondStart.outgoingEdges.first().let {
          it.label.getFlatLabels().isEmpty() && it.target != loopStart
        }
    ) {
      loopCondStart = loopCondStart.outgoingEdges.first().target
    }

    val exits =
      loopLocs
        .mapNotNull { loc ->
          loc.outgoingEdges
            .filter { it.target !in loopLocs }
            .takeIf { it.isNotEmpty() }
            ?.let { loc to it }
        }
        .toMap()

    return Loop(
      loopStart = loopStart,
      loopCondStart = loopCondStart,
      loopLocs = loopLocs,
      loopEdges = loopEdges,
      loopVar = null,
      loopVarInit = null,
      loopVarModifiers = null,
      loopStartEdges = emptyList(),
      exitEdges = exits,
      properlyUnrollable = false,
      forceUnrollLimit = forceUnrollLimit,
      substituteLoopVar = substituteLoopVar,
      parseContext = parseContext,
      collapseBusyWaits = collapseBusyWaits,
      globalVars = globalVars,
    )
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
        // Never for a global loop variable: another thread could write it, so its per-iteration
        // value is not a constant of the copy, and baking one in would hide a race or a
        // memory-safety violation on whatever the loop indexes.
        substituteLoopVar =
          substituteLoopVar && builder.parent.getVars().none { it.wrappedVar == loopVar },
        parseContext = parseContext,
        collapseBusyWaits = collapseBusyWaits,
        globalVars = globalVars,
      )
      .also { if (it in testedLoops) return null }
  }
}
