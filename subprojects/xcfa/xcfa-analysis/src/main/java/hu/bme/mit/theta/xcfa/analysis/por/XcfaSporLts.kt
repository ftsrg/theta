/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getXcfaLts
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.isAtomicBegin
import hu.bme.mit.theta.xcfa.isAtomicEnd
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import java.util.function.Predicate
import kotlin.random.Random

/**
 * LTS with a POR (Partial Order Reduction) algorithm applied as a filter when returning enabled actions.
 *
 * @param xcfa the XCFA of the verified program
 */
open class XcfaSporLts(protected val xcfa: XCFA) : LTS<XcfaState<*>, XcfaAction> {

    companion object {

        private val random: Random = Random.Default
        private val simpleXcfaLts = getXcfaLts()
    }

    /* CACHE COLLECTIONS */

    /**
     * Shared objects (~global variables) used by a transition.
     */
    private val usedSharedObjects: MutableMap<XcfaEdge, Set<Decl<out Type>>> = mutableMapOf()

    /**
     * Shared objects (~global variables) that are used by the key transition or by transitions reachable from the
     * current state via a given transition.
     */
    private val influencedSharedObjects: MutableMap<XcfaEdge, Set<Decl<out Type>>> = mutableMapOf()

    /**
     * Backward transitions in the transition system (a transition of a loop).
     */
    private val backwardTransitions: MutableSet<XcfaEdge> = mutableSetOf()

    init {
        collectBackwardTransitions()
    }

    /**
     * Returns the enabled actions in the ARG from the given state filtered with a POR algorithm.
     *
     * @param state the state whose enabled actions we would like to know
     * @return the enabled actions
     */
    override fun getEnabledActionsFor(state: XcfaState<*>): Set<XcfaAction> {
        // Collecting enabled actions
        val allEnabledActions = getAllEnabledActionsFor(state)

        // Calculating the persistent set starting from every (or some of the) enabled transition; the minimal persistent set is stored
        var minimalPersistentSet = setOf<XcfaAction>()
        val persistentSetFirstActions = getPersistentSetFirstActions(allEnabledActions)
        for (firstActions in persistentSetFirstActions) {
            val persistentSet = calculatePersistentSet(allEnabledActions, firstActions)
            if (minimalPersistentSet.isEmpty() || persistentSet.size < minimalPersistentSet.size) {
                minimalPersistentSet = persistentSet
            }
        }
        return minimalPersistentSet
    }

    /**
     * Returns all enabled actions in the given state.
     *
     * @param state the state whose enabled actions we would like to know
     * @return the enabled actions
     */
    protected fun getAllEnabledActionsFor(state: XcfaState<*>): Collection<XcfaAction> =
        simpleXcfaLts.getEnabledActionsFor(state)

    /**
     * Returns the possible starting actions of a persistent set.
     *
     * @param allEnabledActions the enabled actions in the present state
     * @return the possible starting actions of a persistent set
     */
    protected fun getPersistentSetFirstActions(
        allEnabledActions: Collection<XcfaAction>): Collection<Collection<XcfaAction>> {
        val enabledActionsByProcess = allEnabledActions.groupBy(XcfaAction::pid)
        val enabledProcesses = enabledActionsByProcess.keys.toList().shuffled(random)
        return enabledProcesses.map { checkNotNull(enabledActionsByProcess[it]) }
    }

    /**
     * Calculates a persistent set of enabled actions starting from a particular action.
     *
     * @param enabledActions the enabled actions in the present state
     * @param firstActions   the actions that will be added to the persistent set as the first actions
     * @return a persistent set of enabled actions
     */
    private fun calculatePersistentSet(enabledActions: Collection<XcfaAction>,
        firstActions: Collection<XcfaAction>): Set<XcfaAction> {
        if (firstActions.any(::isBackwardAction)) {
            return enabledActions.toSet()
        }
        val persistentSet = firstActions.toMutableSet()
        val otherActions = (enabledActions.toMutableSet() subtract persistentSet).toMutableSet() // actions not in the persistent set
        var addedNewAction = true
        while (addedNewAction) {
            addedNewAction = false
            val actionsToRemove = mutableSetOf<XcfaAction>()
            for (action in otherActions) {
                // for every action that is not in the persistent set it is checked whether it should be added to the persistent set
                // (because it is dependent with an action already in the persistent set)
                if (persistentSet.any { persistentSetAction -> areDependents(persistentSetAction, action) }) {
                    if (isBackwardAction(action)) {
                        return enabledActions.toSet() // see POR algorithm for the reason of removing backward transitions
                    }
                    persistentSet.add(action)
                    actionsToRemove.add(action)
                    addedNewAction = true
                }
            }
            actionsToRemove.forEach(otherActions::remove)
        }
        return persistentSet
    }

    /**
     * Determines whether an action is dependent with another one (based on the notions introduced for the POR
     * algorithm) already in the persistent set.
     *
     * @param persistentSetAction the action in the persistent set
     * @param action              the other action (not in the persistent set)
     * @return true, if the two actions are dependent in the context of persistent sets
     */
    private fun areDependents(persistentSetAction: XcfaAction, action: XcfaAction): Boolean {
        val usedByPersistentSetAction = getCachedUsedSharedObjects(getEdgeOf(persistentSetAction))
        return isSameProcess(persistentSetAction, action) ||
            getInfluencedSharedObjects(getEdgeOf(action)).any { it in usedByPersistentSetAction }
    }

    /**
     * Determines whether two actions are in the same process.
     *
     * @param action1 the first action
     * @param action2 the second action
     * @return true, if the two actions are in the same process
     */
    protected fun isSameProcess(action1: XcfaAction, action2: XcfaAction) = action1.pid == action2.pid

    /**
     * Returns the global variables that an edge uses (it is present in one of its labels).
     *
     * @param edge whose global variables are to be returned
     * @return the set of used global variables
     */
    private fun getDirectlyUsedSharedObjects(edge: XcfaEdge): Set<VarDecl<out Type>> {
        val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar)
        return edge.getFlatLabels().flatMap { label ->
            label.collectVars().filter { it in globalVars }
        }.toSet()
    }

    /**
     * Returns the global variables that an edge uses or if it is the start of an atomic block the global variables
     * that are used in the atomic block.
     *
     * @param edge whose global variables are to be returned
     * @return the set of directly or indirectly used global variables
     */
    private fun getUsedSharedObjects(edge: XcfaEdge): Set<Decl<out Type>> =
        if (edge.getFlatLabels().any(XcfaLabel::isAtomicBegin)) {
            getSharedObjectsWithBFS(edge) {
                it.getFlatLabels().none(XcfaLabel::isAtomicEnd)
            }.toSet()
        } else {
            getDirectlyUsedSharedObjects(edge)
        }

    /**
     * Same as [getUsedSharedObjects] with an additional cache layer.
     *
     * @param edge whose shared objects are to be returned
     * @return the set of directly or indirectly used shared objects
     */
    protected fun getCachedUsedSharedObjects(edge: XcfaEdge): Set<Decl<out Type>> {
        if (!usedSharedObjects.containsKey(edge)) {
            val vars = getUsedSharedObjects(edge)
            usedSharedObjects[edge] = vars
        }
        return usedSharedObjects[edge]!!
    }

    /**
     * Returns the shared objects (~global variables) used by the given transition or by transitions that are reachable
     * via the given transition ("influenced shared objects").
     *
     * @param edge whose successor transitions' shared objects are to be returned.
     * @return the set of influenced shared objects
     */
    protected fun getInfluencedSharedObjects(edge: XcfaEdge): Set<Decl<out Type>> {
        if (!influencedSharedObjects.containsKey(edge)) {
            influencedSharedObjects[edge] = getSharedObjectsWithBFS(edge) { true }
        }
        return influencedSharedObjects[edge]!!
    }

    /**
     * Returns shared objects (~global variables) encountered in a search starting from a given transition.
     *
     * @param startTransition the start point (transition) of the search
     * @param goFurther       the predicate that tells whether more transitions have to be explored through this
     * transition
     * @return the set of encountered shared objects
     */
    private fun getSharedObjectsWithBFS(startTransition: XcfaEdge,
        goFurther: Predicate<XcfaEdge>): Set<Decl<out Type>> {
        val vars = mutableSetOf<Decl<out Type>>()
        val exploredTransitions = mutableListOf<XcfaEdge>()
        val transitionsToExplore = mutableListOf<XcfaEdge>()
        transitionsToExplore.add(startTransition)
        while (transitionsToExplore.isNotEmpty()) {
            val exploring = transitionsToExplore.removeFirst()
            vars.addAll(getDirectlyUsedSharedObjects(exploring))
            if (goFurther.test(exploring)) {
                val successiveTransitions = getSuccessiveTransitions(exploring)
                for (newTransition in successiveTransitions) {
                    if (newTransition !in exploredTransitions) {
                        transitionsToExplore.add(newTransition)
                    }
                }
            }
            exploredTransitions.add(exploring)
        }
        return vars
    }

    /**
     * Returns the xcfa edge of the given action.
     *
     * @param action the action whose edge is to be returned
     * @return the edge of the action
     */
    protected fun getEdgeOf(action: XcfaAction) = action.edge

    /**
     * Returns the outgoing edges of the target of the given edge.
     *
     * @param edge the edge whose target's outgoing edges are to be returned
     * @return the outgoing edges of the target of the edge
     */
    private fun getSuccessiveTransitions(edge: XcfaEdge): Set<XcfaEdge> {
        val outgoingEdges = edge.target.outgoingEdges.toMutableSet()
        val startThreads = edge.getFlatLabels().filterIsInstance<StartLabel>().toList()
        if (startThreads.isNotEmpty()) { // for start thread labels, the thread procedure must be explored, too!
            startThreads.forEach { startThread ->
                outgoingEdges.addAll(
                    xcfa.procedures.first { it.name == startThread.name }.initLoc.outgoingEdges)
            }
        }
        return outgoingEdges
    }

    /**
     * Determines whether the given action is a backward action.
     *
     * @param action the action to be classified as backward action or non-backward action
     * @return true, if the action is a backward action
     */
    protected fun isBackwardAction(action: XcfaAction): Boolean = backwardTransitions.contains(getEdgeOf(action))

    /**
     * Collects backward edges of the given XCFA.
     */
    private fun collectBackwardTransitions() {
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
                    if (visitedLocations.contains(target)) { // backward edge
                        backwardTransitions.add(outgoingEdge)
                    } else {
                        stack.push(target)
                    }
                }
            }
        }
    }
}