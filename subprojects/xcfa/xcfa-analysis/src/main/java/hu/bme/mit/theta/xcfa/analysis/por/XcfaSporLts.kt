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

import hu.bme.mit.theta.analysis.algorithm.SporLts
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
import kotlin.random.Random

open class XcfaSporLts(protected val xcfa: XCFA) : SporLts<XcfaState<*>, XcfaAction, XcfaEdge>() {

    companion object {

        private val random: Random = Random.Default
        private val simpleXcfaLts = getXcfaLts()
    }

    init {
        collectBackwardTransitions()
    }

    override fun getAllEnabledActionsFor(state: XcfaState<*>): Collection<XcfaAction> =
        simpleXcfaLts.getEnabledActionsFor(state)

    override fun getPersistentSetFirstActions(
        allEnabledActions: Collection<XcfaAction>): Collection<Collection<XcfaAction>> {
        val enabledActionsByProcess = allEnabledActions.groupBy(XcfaAction::pid)
        val enabledProcesses = enabledActionsByProcess.keys.toList().shuffled(random)
        return enabledProcesses.map { checkNotNull(enabledActionsByProcess[it]) }
    }

    override fun isSameProcess(action1: XcfaAction,
        action2: XcfaAction) = action1.pid == action2.pid

    override fun getTransitionOf(action: XcfaAction) = action.edge

    override fun getSuccessiveTransitions(edge: XcfaEdge): Set<XcfaEdge> {
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
     * Returns the global variables that an edge uses (it is present in one of its labels).
     *
     * @param edge whose global variables are to be returned
     * @return the set of used global variables
     */
    override fun getDirectlyUsedSharedObjects(edge: XcfaEdge): Set<VarDecl<out Type?>> {
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
    override fun getUsedSharedObjects(edge: XcfaEdge): Set<Decl<out Type?>?> =
        if (edge.getFlatLabels().any(XcfaLabel::isAtomicBegin)) {
            getSharedObjectsWithBFS(edge) {
                it.getFlatLabels().none(XcfaLabel::isAtomicEnd)
            }.toSet()
        } else {
            getDirectlyUsedSharedObjects(edge)
        }

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