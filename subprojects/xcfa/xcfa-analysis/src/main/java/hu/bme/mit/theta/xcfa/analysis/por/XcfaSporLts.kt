/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.function.Predicate
import kotlin.random.Random

/**
 * LTS with a POR (Partial Order Reduction) algorithm applied as a filter when returning enabled actions.
 * The algorithm is similar to the static source-set based POR algorithm described in the following paper:
 * Abdulla, P., Aronis, S., Jonsson, B., Sagonas, K. (2017):
 * Comparing source sets and persistent sets for partial order reduction
 *
 * @param xcfa the XCFA of the verified program
 */
open class XcfaSporLts(protected val xcfa: XCFA) : LTS<XcfaState<out PtrState<out ExprState>>, XcfaAction> {

    companion object {

        var random: Random = Random.Default
    }

    protected var simpleXcfaLts = getXcfaLts()

    /* CACHE COLLECTIONS */

    /**
     * Global variables used by an edge.
     */
    private val usedVars: MutableMap<XcfaEdge, Set<VarDecl<*>>> = mutableMapOf()

    /**
     * Global variables that are used by the key edge or by edges reachable from the
     * current state via a given edge.
     */
    private val influencedVars: MutableMap<XcfaEdge, Set<VarDecl<*>>> = mutableMapOf()

    /**
     * Backward edges in the CFA (an edge of a loop).
     */
    private val backwardEdges: MutableSet<Pair<XcfaLocation, XcfaLocation>> = mutableSetOf()

    /**
     * Variables associated to mutex identifiers. TODO: this should really be solved by storing VarDecls in FenceLabel.
     */
    protected val fenceVars: MutableMap<String, VarDecl<*>> = mutableMapOf()
    private val String.fenceVar get() = fenceVars.getOrPut(this) { Decls.Var(this, Bool()) }

    init {
        collectBackwardEdges()
    }

    /**
     * Returns the enabled actions in the ARG from the given state filtered with a POR algorithm.
     *
     * @param state the state whose enabled actions we would like to know
     * @return the enabled actions
     */
    override fun getEnabledActionsFor(state: XcfaState<out PtrState<out ExprState>>): Set<XcfaAction> {
        // Collecting enabled actions
        val allEnabledActions = simpleXcfaLts.getEnabledActionsFor(state)

        // Calculating the source set starting from every (or some of the) enabled transition; the minimal source set is stored
        var minimalSourceSet = setOf<XcfaAction>()
        val sourceSetFirstActions = getSourceSetFirstActions(state, allEnabledActions)
        for (firstActions in sourceSetFirstActions) {
            val sourceSet = calculateSourceSet(allEnabledActions, firstActions)
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
        allEnabledActions: Collection<XcfaAction>
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
     * Checks whether a process is blocked by a mutex and if it is, it adds the process that blocks it to the set of
     * first processes.
     *
     * @param state the current state
     * @param pid the process whose blocking is to be checked
     * @param firstProcesses the set of first processes
     * @param enabledActionsByProcess the enabled actions grouped by processes
     * @return the set of first processes
     */
    private fun checkMutexBlocks(
        state: XcfaState<out PtrState<out ExprState>>, pid: Int, firstProcesses: MutableSet<Int>,
        enabledActionsByProcess: Map<Int, List<XcfaAction>>
    ) {
        val processState = checkNotNull(state.processes[pid])
        if (!processState.paramsInitialized) return
        val disabledOutEdges = processState.locs.peek().outgoingEdges.filter { edge ->
            enabledActionsByProcess[pid]?.none { action -> action.target == edge.target } ?: true
        }
        disabledOutEdges.forEach { edge ->
            edge.getFlatLabels().filterIsInstance<FenceLabel>().forEach { fence ->
                fence.labels.filter { it.startsWith("mutex_lock") }.forEach { lock ->
                    val mutex = lock.substringAfter('(').substringBefore(')')
                    state.mutexes[mutex]?.let { pid2 ->
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
     * @param firstActions   the actions that will be added to the source set as the first actions
     * @return a source set of enabled actions
     */
    private fun calculateSourceSet(
        enabledActions: Collection<XcfaAction>,
        firstActions: Collection<XcfaAction>
    ): Set<XcfaAction> {
        if (firstActions.any { it.isBackward }) {
            return enabledActions.toSet()
        }
        val sourceSet = firstActions.toMutableSet()
        val otherActions =
            (enabledActions.toMutableSet() subtract sourceSet).toMutableSet() // actions not in the source set
        var addedNewAction = true
        while (addedNewAction) {
            addedNewAction = false
            val actionsToRemove = mutableSetOf<XcfaAction>()
            for (action in otherActions) {
                // for every action that is not in the source set it is checked whether it should be added to the source set
                // (because it is dependent with an action already in the source set)
                if (sourceSet.any { areDependents(it, action) }) {
                    if (action.isBackward) {
                        return enabledActions.toSet() // see POR algorithm for the reason of handling backward edges this way
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
     * Determines whether an action is dependent with another one (based on the notions introduced for the POR
     * algorithm) already in the source set.
     *
     * @param sourceSetAction the action in the source set
     * @param action          the other action (not in the source set)
     * @return true, if the two actions are dependent in the context of source sets
     */
    private fun areDependents(sourceSetAction: XcfaAction, action: XcfaAction): Boolean {
        if (sourceSetAction.pid == action.pid) return true

        val sourceSetActionVars = getCachedUsedVars(getEdge(sourceSetAction))
        val influencedVars = getInfluencedVars(getEdge(action))
        if ((influencedVars intersect sourceSetActionVars).isNotEmpty()) return true

        // precise pointer information for current action
        //val sourceSetActionMemLocs = sourceSetAction.preciseMemoryLocations
        val sourceSetActionMemLocs = sourceSetActionVars.flatMap { xcfa.pointsToGraph[it] ?: listOf() }.toSet()
        // imprecise pointer information for future actions
        val influencedMemLocs = influencedVars.flatMap { xcfa.pointsToGraph[it] ?: listOf() }.toSet()
        return (sourceSetActionMemLocs intersect influencedMemLocs).isNotEmpty()
    }

    /**
     * Returns the global variables that an edge uses (it is present in one of its labels).
     * Mutex variables are also considered to avoid running into a deadlock and stop exploration.
     *
     * @param edge whose global variables are to be returned
     * @return the set of used global variables
     */
    private fun getDirectlyUsedVars(edge: XcfaEdge): Set<VarDecl<*>> {
        val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar)
        return edge.getFlatLabels().flatMap { label ->
            label.collectVars().filter { it in globalVars } union
                ((label as? FenceLabel)?.labels
                    ?.filter { it.startsWith("start_cond_wait") || it.startsWith("cond_signal") }
                    ?.map { it.substringAfter("(").substringBefore(")").split(",")[0] }
                    ?.map { it.fenceVar } ?: listOf())
        }.toSet() union edge.acquiredEmbeddedFenceVars.let { mutexes ->
            if (mutexes.size <= 1) setOf() else mutexes.map { it.fenceVar }
        }
    }

    /**
     * Returns the global variables that an edge uses or if it is the start of an atomic block the global variables
     * that are used in the atomic block. The result is cached.
     *
     * @param edge whose global variables are to be returned
     * @return the set of directly or indirectly used global variables
     */
    protected fun getCachedUsedVars(edge: XcfaEdge): Set<VarDecl<*>> {
        if (edge in usedVars) return usedVars[edge]!!
        val flatLabels = edge.getFlatLabels()
        val mutexes = flatLabels.filterIsInstance<FenceLabel>().flatMap { it.acquiredMutexes }.toMutableSet()
        val vars = if (mutexes.isEmpty()) {
            getDirectlyUsedVars(edge)
        } else {
            getVarsWithBFS(edge) { it.mutexOperations(mutexes) }.toSet()
        }
        usedVars[edge] = vars
        return vars
    }

    /**
     * Returns the global variables used by the given edge or by edges that are reachable
     * via the given edge ("influenced vars").
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
     * Returns global variables encountered in a search starting from a given edge.
     *
     * @param startEdge the start point of the search
     * @param goFurther the predicate that tells whether more edges have to be explored through this edge
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
     * Returns the xcfa edge of the given action.
     *
     * @param action the action whose edge is to be returned
     * @return the edge of the action
     */
    protected open fun getEdge(action: XcfaAction) = action.edge

    /**
     * Returns the outgoing edges of the target of the given edge. For start threads, the first edges of the started
     * procedures are also included.
     *
     * @param edge the edge whose target's outgoing edges are to be returned
     * @return the outgoing edges of the target of the edge
     */
    private fun getSuccessiveEdges(edge: XcfaEdge): Set<XcfaEdge> {
        val outgoingEdges = edge.target.outgoingEdges.toMutableSet()
        val startThreads = edge.getFlatLabels().filterIsInstance<StartLabel>().toList()
        if (startThreads.isNotEmpty()) { // for start thread labels, the thread procedure must be explored, too!
            startThreads.forEach { startThread ->
                outgoingEdges.addAll(xcfa.procedures.first { it.name == startThread.name }.initLoc.outgoingEdges)
            }
        }
        return outgoingEdges
    }

    /**
     * Determines whether this action is a backward action.
     *
     * @return true, if the action is a backward action
     */
    protected open val XcfaAction.isBackward: Boolean get() = backwardEdges.any { it.first == source && it.second == target }

    /**
     * Collects backward edges of the given XCFA.
     */
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