/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.*
import java.util.*
import java.util.function.Predicate
import kotlin.random.Random

typealias MemLoc = Pair<Expr<*>, Expr<*>>

internal fun MemLoc.isLit() = first is LitExpr<*> && second is LitExpr<*>

/**
 * LTS with a POR (Partial Order Reduction) algorithm applied as a filter when returning enabled
 * actions. The algorithm is similar to the static source-set based POR algorithm described in the
 * following paper: Abdulla, P., Aronis, S., Jonsson, B., Sagonas, K. (2017): Comparing source sets
 * and persistent sets for partial order reduction
 *
 * @param xcfa the XCFA of the verified program
 */
open class XcfaSporLts(protected val xcfa: XCFA) :
  LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction> {

  companion object {

    private val dependencySolver: Solver = Z3SolverFactory.getInstance().createSolver()
    var random: Random = Random.Default
  }

  protected var simpleXcfaLts = getXcfaLts()

  /* CACHE COLLECTIONS */

  /** Global variables used by an edge. */
  private val usedVars: MutableMap<XcfaEdge, Set<VarDecl<*>>> = mutableMapOf()

  private val usedMemLocs: MutableMap<XcfaEdge, Set<MemLoc>> = mutableMapOf()

  /**
   * Global variables that are used by the key edge or by edges reachable from the current state via
   * a given edge.
   */
  private val influencedVars: MutableMap<XcfaEdge, Set<VarDecl<*>>> = mutableMapOf()
  private val influencedMemLocs: MutableMap<XcfaEdge, Set<MemLoc>> = mutableMapOf()

  /** Backward edges in the CFA (an edge of a loop). */
  private val backwardEdges: MutableSet<Pair<XcfaLocation, XcfaLocation>> = mutableSetOf()

  /** Variables of mutex handles (VarDecls in FenceLabels), needed for AASPOR. */
  protected val fenceVars: MutableSet<VarDecl<*>> = mutableSetOf()

  init {
    collectBackwardEdges()
  }

  /**
   * Returns the enabled actions in the ARG from the given state filtered with a POR algorithm.
   *
   * @param state the state whose enabled actions we would like to know
   * @return the enabled actions
   */
  override fun getEnabledActionsFor(
    state: XcfaState<out PtrState<out ExprState>>
  ): Set<XcfaAction> = getEnabledActionsFor(state, simpleXcfaLts.getEnabledActionsFor(state))

  /**
   * Calculates the source set starting from every (or some of the) enabled transition; the minimal
   * source set is returned.
   */
  protected open fun getEnabledActionsFor(
    state: XcfaState<out PtrState<out ExprState>>,
    allEnabledActions: Collection<XcfaAction>,
  ): Set<XcfaAction> {
    var minimalSourceSet = setOf<XcfaAction>()
    val sourceSetFirstActions = getSourceSetFirstActions(state, allEnabledActions)
    for (firstActions in sourceSetFirstActions) {
      val sourceSet = calculateSourceSet(state, allEnabledActions, firstActions)
      if (minimalSourceSet.isEmpty() || sourceSet.size < minimalSourceSet.size) {
        minimalSourceSet = sourceSet
      }
    }
    return minimalSourceSet
  }

  /**
   * Returns the possible starting actions of a source set.
   *
   * @param allEnabledActions the enabled actions in the present state
   * @return the possible starting actions of a source set
   */
  protected fun getSourceSetFirstActions(
    state: XcfaState<out PtrState<out ExprState>>,
    allEnabledActions: Collection<XcfaAction>,
  ): Collection<Collection<XcfaAction>> {
    val enabledActionsByProcess = allEnabledActions.groupBy(XcfaAction::pid)
    val enabledProcesses = enabledActionsByProcess.keys.toList().shuffled(random)
    return enabledProcesses.map { pid ->
      val firstProcesses = mutableSetOf(pid)
      checkMutexBlocks(state, pid, firstProcesses, enabledActionsByProcess)
      firstProcesses.flatMap { enabledActionsByProcess[it] ?: emptyList() }
    }
  }

  /**
   * Checks whether a process is blocked by a mutex and if it is, it adds the process that blocks it
   * to the set of first processes.
   *
   * @param state the current state
   * @param pid the process whose blocking is to be checked
   * @param firstProcesses the set of first processes
   * @param enabledActionsByProcess the enabled actions grouped by processes
   * @return the set of first processes
   */
  private fun checkMutexBlocks(
    state: XcfaState<out PtrState<out ExprState>>,
    pid: Int,
    firstProcesses: MutableSet<Int>,
    enabledActionsByProcess: Map<Int, List<XcfaAction>>,
  ) {
    val processState = state.processes[pid]!!
    if (!processState.paramsInitialized) return
    val disabledOutEdges =
      processState.locs.peek().outgoingEdges.filter { edge ->
        enabledActionsByProcess[pid]?.none { action -> action.target == edge.target } ?: true
      }
    disabledOutEdges.forEach { edge ->
      edge.getFlatLabels().filterIsInstance<FenceLabel>().forEach { fence ->
        fence.blockingMutexesWithoutAtomic.forEach { mutex ->
          state.mutexes[mutex.name]?.let { pid2 ->
            if (pid2 !in firstProcesses) {
              firstProcesses.add(pid2)
              checkMutexBlocks(state, pid2, firstProcesses, enabledActionsByProcess)
            }
          }
        }
      }
    }
  }

  /**
   * Calculates a source set of enabled actions starting from a particular action.
   *
   * @param enabledActions the enabled actions in the present state
   * @param firstActions the actions that will be added to the source set as the first actions
   * @return a source set of enabled actions
   */
  private fun calculateSourceSet(
    state: XcfaState<out PtrState<out ExprState>>,
    enabledActions: Collection<XcfaAction>,
    firstActions: Collection<XcfaAction>,
  ): Set<XcfaAction> {
    if (firstActions.any { it.isBackward }) {
      return enabledActions.toSet()
    }
    val sourceSet = firstActions.toMutableSet()
    val otherActions =
      (enabledActions.toMutableSet() subtract sourceSet)
        .toMutableSet() // actions not in the source set
    var addedNewAction = true
    while (addedNewAction) {
      addedNewAction = false
      val actionsToRemove = mutableSetOf<XcfaAction>()
      for (action in otherActions) {
        // for every action that is not in the source set it is checked whether it should be added
        // to the source set
        // (because it is dependent with an action already in the source set)
        if (sourceSet.any { dependent(state, it, action) }) {
          if (action.isBackward) {
            return enabledActions
              .toSet() // see POR algorithm for the reason of handling backward edges this way
          }
          sourceSet.add(action)
          actionsToRemove.add(action)
          addedNewAction = true
        }
      }
      actionsToRemove.forEach(otherActions::remove)
    }
    return sourceSet
  }

  /**
   * Determines whether an action is dependent with another one (based on the notions introduced for
   * the POR algorithm) already in the source set.
   *
   * @param sourceSetAction the action in the source set
   * @param action the other action (not in the source set)
   * @return true, if the two actions are dependent in the context of source sets
   */
  private fun dependent(
    state: XcfaState<out PtrState<out ExprState>>,
    sourceSetAction: XcfaAction,
    action: XcfaAction,
  ): Boolean {
    if (sourceSetAction.pid == action.pid) return true

    val sourceSetActionVars = getCachedUsedVars(getEdge(sourceSetAction))
    val influencedVars = getInfluencedVars(getEdge(action))
    if ((influencedVars intersect sourceSetActionVars).isNotEmpty()) return true

    val sourceSetMemLocs = getCachedMemLocs(getEdge(sourceSetAction))
    val influencedMemLocs = getInfluencedMemLocs(getEdge(action))
    if (
      (influencedMemLocs.filter(MemLoc::isLit) intersect
          sourceSetMemLocs.filter(MemLoc::isLit).toSet())
        .isNotEmpty()
    )
      return true

    return indirectlyDependent(state, sourceSetAction, sourceSetMemLocs, influencedMemLocs)
  }

  /**
   * Currently, the check only tests the first argument of (deref arr off), and deems two actions
   * dependent if the array values may overlap. This should probably be extended for offsets as
   * well.
   */
  protected fun indirectlyDependent(
    state: XcfaState<out PtrState<out ExprState>>,
    sourceSetAction: XcfaAction,
    sourceSetMemLocs: Set<MemLoc>,
    inflMemLocs: Set<MemLoc>,
  ): Boolean {
    val sourceSetActionMemLocs = memLocsToLitExprs(sourceSetMemLocs) ?: return true
    val influencedMemLocs = memLocsToLitExprs(inflMemLocs) ?: return true
    val intersection = intersect(sourceSetActionMemLocs, influencedMemLocs)
    if (intersection.isEmpty())
      return false // they cannot point to the same memory location even based on static info

    if (sourceSetMemLocs.all { it.first is LitExpr<*> })
      return true // there is no uncertainty in the current memory locations, and they intersect

    val derefs = sourceSetAction.label.dereferences
    var expr: Expr<BoolType> =
      Or(
        intersection.flatMap { memLoc ->
          derefs.map { And(Eq(memLoc.first, it.array), Eq(memLoc.second, it.offset)) }
        }
      )
    expr =
      (state.sGlobal.innerState as? ExplState)?.let { s -> ExprUtils.simplify(expr, s.`val`) }
        ?: ExprUtils.simplify(expr)
    if (expr == True()) return true
    return WithPushPop(dependencySolver).use {
      dependencySolver.add(PathUtils.unfold(state.sGlobal.toExpr(), 0))
      dependencySolver.add(
        PathUtils.unfold(expr, 0)
      ) // is it always given that the state will produce 0 indexed constants?
      dependencySolver.check().isSat // two pointers may point to the same memory location
    }
  }

  private fun exprToLitExpr(expr: Expr<*>): Set<LitExpr<*>>? =
    if (expr is LitExpr<*>) setOf(expr) else expr.pointsTo(xcfa)

  private fun memLocsToLitExprs(
    memLocs: Set<MemLoc>
  ): List<Pair<Set<LitExpr<*>>, Set<LitExpr<*>>>>? =
    memLocs.map {
      val first = exprToLitExpr(it.first) ?: return null
      val second = exprToLitExpr(it.second) ?: return null
      first to second
    }

  private fun intersect(
    memlocs1: List<Pair<Set<LitExpr<*>>, Set<LitExpr<*>>>>,
    memlocs2: List<Pair<Set<LitExpr<*>>, Set<LitExpr<*>>>>,
  ): Set<Pair<LitExpr<*>, LitExpr<*>>> {
    val intersection = mutableSetOf<Pair<LitExpr<*>, LitExpr<*>>>()
    for (memloc1 in memlocs1) {
      for (memloc2 in memlocs2) {
        val firsts = memloc1.first intersect memloc2.first
        val seconds = memloc1.second intersect memloc2.second
        for (f in firsts) {
          for (s in seconds) {
            intersection.add(f to s)
          }
        }
      }
    }
    return intersection
  }

  /**
   * Returns the global variables that an edge uses (it is present in one of its labels). Mutex
   * variables are also considered to avoid running into a deadlock and stop exploration.
   *
   * @param edge whose global variables are to be returned
   * @return the set of used global variables
   */
  private fun getDirectlyUsedVars(edge: XcfaEdge): Set<VarDecl<*>> {
    val globalVars = xcfa.globalVars.map(XcfaGlobalVar::wrappedVar)
    fenceVars.addAll(edge.fenceVars)
    return edge
      .getFlatLabels()
      .flatMap { label -> label.collectVars().filter { it in globalVars } }
      .toSet() union
      edge.acquiredEmbeddedFenceVars.let { mutexes ->
        fenceVars.addAll(mutexes)
        if (mutexes.size <= 1) setOf() else mutexes
      }
  }

  /**
   * Returns the base-offset pairs that an edge uses (it is present in one of its labels).
   *
   * @param edge whose base-offset pairs are to be returned
   * @return the set of used global variables
   */
  private fun getDirectlyUsedMemLocs(edge: XcfaEdge): Set<MemLoc> {
    return edge
      .getFlatLabels()
      .flatMap { label -> label.dereferences.map { Pair(it.array, it.offset) } }
      .toSet()
  }

  /**
   * Returns the global variables that an edge uses or if it is the start of an atomic block the
   * global variables that are used in the atomic block. The result is cached.
   *
   * @param edge whose global variables are to be returned
   * @return the set of directly or indirectly used global variables
   */
  protected fun getCachedUsedVars(edge: XcfaEdge): Set<VarDecl<*>> {
    if (edge in usedVars) return usedVars[edge]!!
    val flatLabels = edge.getFlatLabels()
    val mutexes =
      flatLabels.filterIsInstance<FenceLabel>().flatMap { it.acquiredMutexes }.toMutableSet()
    val vars =
      if (mutexes.isEmpty()) {
        getDirectlyUsedVars(edge)
      } else {
        getVarsWithBFS(edge) { it.mutexOperations(mutexes) }.toSet()
      }
    usedVars[edge] = vars
    return vars
  }

  /**
   * Returns the base-offset pairs that an edge uses. The result is cached.
   *
   * @param edge whose base-offset pairs are collected
   * @return the set of directly or indirectly used base-offset pairs
   */
  protected fun getCachedMemLocs(edge: XcfaEdge): Set<MemLoc> {
    if (edge in usedMemLocs) return usedMemLocs[edge]!!
    val flatLabels = edge.getFlatLabels()
    val mutexes =
      flatLabels.filterIsInstance<FenceLabel>().flatMap { it.acquiredMutexes }.toMutableSet()
    val vars =
      if (mutexes.isEmpty()) {
        getDirectlyUsedMemLocs(edge)
      } else {
        getMemLocsWithBFS(edge) { it.mutexOperations(mutexes) }.toSet()
      }
    usedMemLocs[edge] = vars
    return vars
  }

  /**
   * Returns the global variables used by the given edge or by edges that are reachable via the
   * given edge ("influenced vars").
   *
   * @param edge whose successor edges' global variables are to be returned.
   * @return the set of influenced global variables
   */
  protected fun getInfluencedVars(edge: XcfaEdge): Set<VarDecl<*>> {
    if (edge in influencedVars) return influencedVars[edge]!!
    val vars = getVarsWithBFS(edge) { true }
    influencedVars[edge] = vars
    return vars
  }

  /**
   * Returns the base-offset pairs used by the given edge or by edges that are reachable via the
   * given edge ("influenced memlocs").
   *
   * @param edge whose successor edges' base-offset pairs are to be returned.
   * @return the set of influenced global variables
   */
  protected fun getInfluencedMemLocs(edge: XcfaEdge): Set<MemLoc> {
    if (edge in influencedMemLocs) return influencedMemLocs[edge]!!
    val vars = getMemLocsWithBFS(edge) { true }
    influencedMemLocs[edge] = vars
    return vars
  }

  /**
   * Returns global variables encountered in a search starting from a given edge.
   *
   * @param startEdge the start point of the search
   * @param goFurther the predicate that tells whether more edges have to be explored through this
   *   edge
   * @return the set of encountered global variables
   */
  private fun getVarsWithBFS(startEdge: XcfaEdge, goFurther: Predicate<XcfaEdge>): Set<VarDecl<*>> {
    val vars = mutableSetOf<VarDecl<*>>()
    val exploredEdges = mutableListOf<XcfaEdge>()
    val edgesToExplore = mutableListOf<XcfaEdge>()
    edgesToExplore.add(startEdge)
    while (edgesToExplore.isNotEmpty()) {
      val exploring = edgesToExplore.removeFirst()
      vars.addAll(getDirectlyUsedVars(exploring))
      if (goFurther.test(exploring)) {
        val successiveEdges = getSuccessiveEdges(exploring)
        for (newEdge in successiveEdges) {
          if (newEdge !in exploredEdges) {
            edgesToExplore.add(newEdge)
          }
        }
      }
      exploredEdges.add(exploring)
    }
    return vars
  }

  /**
   * Returns base-offset pairs encountered in a search starting from a given edge.
   *
   * @param startEdge the start point of the search
   * @param goFurther the predicate that tells whether more edges have to be explored through this
   *   edge
   * @return the set of encountered base-offset variables
   */
  private fun getMemLocsWithBFS(startEdge: XcfaEdge, goFurther: Predicate<XcfaEdge>): Set<MemLoc> {
    val memLocs = mutableSetOf<MemLoc>()
    val exploredEdges = mutableListOf<XcfaEdge>()
    val edgesToExplore = mutableListOf<XcfaEdge>()
    edgesToExplore.add(startEdge)
    while (edgesToExplore.isNotEmpty()) {
      val exploring = edgesToExplore.removeFirst()
      memLocs.addAll(getDirectlyUsedMemLocs(exploring))
      if (goFurther.test(exploring)) {
        val successiveEdges = getSuccessiveEdges(exploring)
        for (newEdge in successiveEdges) {
          if (newEdge !in exploredEdges) {
            edgesToExplore.add(newEdge)
          }
        }
      }
      exploredEdges.add(exploring)
    }
    return memLocs
  }

  /**
   * Returns the xcfa edge of the given action.
   *
   * @param action the action whose edge is to be returned
   * @return the edge of the action
   */
  protected open fun getEdge(action: XcfaAction) = action.edge

  /**
   * Returns the outgoing edges of the target of the given edge. For start threads, the first edges
   * of the started procedures are also included.
   *
   * @param edge the edge whose target's outgoing edges are to be returned
   * @return the outgoing edges of the target of the edge
   */
  private fun getSuccessiveEdges(edge: XcfaEdge): Set<XcfaEdge> {
    val outgoingEdges = edge.target.outgoingEdges.toMutableSet()
    val startThreads = edge.getFlatLabels().filterIsInstance<StartLabel>().toList()
    if (
      startThreads.isNotEmpty()
    ) { // for start thread labels, the thread procedure must be explored, too!
      startThreads.forEach { startThread ->
        outgoingEdges.addAll(
          xcfa.procedures.first { it.name == startThread.name }.initLoc.outgoingEdges
        )
      }
    }
    return outgoingEdges
  }

  /**
   * Determines whether this action is a backward action.
   *
   * @return true, if the action is a backward action
   */
  protected open val XcfaAction.isBackward: Boolean
    get() = backwardEdges.any { it.first == source && it.second == target }

  /** Collects backward edges of the given XCFA. */
  private fun collectBackwardEdges() {
    for (procedure in xcfa.procedures) {
      // DFS for every procedure of the XCFA to discover backward edges
      val visitedLocations = mutableSetOf<XcfaLocation>()
      val stack = Stack<XcfaLocation>()

      stack.push(procedure.initLoc) // start from the initial location of the procedure
      while (stack.isNotEmpty()) {
        val visiting = stack.pop()
        visitedLocations.add(visiting)
        for (outgoingEdge in visiting.outgoingEdges) {
          val target = outgoingEdge.target
          if (target in visitedLocations) { // backward edge
            backwardEdges.add(outgoingEdge.source to outgoingEdge.target)
          } else {
            stack.push(target)
          }
        }
      }
    }
  }
}
