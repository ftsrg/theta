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

package hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.Witness
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace

class TraceGenerationSummaryBuilder<S : State, A : Action> {
    val argTraces: MutableList<ArgTrace<S, A>> = mutableListOf()

    fun addTrace(trace: ArgTrace<S, A>) {
        if(argTraces.isNotEmpty()) {
            checkState(argTraces.get(0).node(0)==trace.node(0), "All traces in summary must start with the same node!")
        }
        argTraces.add(trace)
    }

    fun build(): AbstractTraceSummary<S, A> {
        checkState(argTraces.isNotEmpty(), "Summary must have at least one trace in it!")

        val argNodes: Set<ArgNode<S, A>> = argTraces.map { trace -> trace.nodes() }.flatten().toSet()

        // grouping nodes covering each other for state summaries
        val nodeGroups: MutableList<MutableSet<ArgNode<S, A>>> = mutableListOf()
        for (node in argNodes) {
            if (nodeGroups.isEmpty()) {
                nodeGroups.add(mutableSetOf(node))
            } else {
                val inCoverRelationWithNode: MutableList<ArgNode<S, A>> = mutableListOf()
                inCoverRelationWithNode.addAll(node.coveredNodes.toList())
                if (node.coveringNode.isPresent) inCoverRelationWithNode.add(node.coveringNode.get())

                val nodeGroup = nodeGroups.filter(
                    fun(group: MutableSet<ArgNode<S, A>>): Boolean {
                        for (coverNode in inCoverRelationWithNode) {
                            if (group.contains(coverNode)) {
                                return true
                            }
                        }
                        return false
                    }
                ).toList()

                checkState(nodeGroup.size <= 1) // either found one where node would fit OR found none and will create new one
                if(nodeGroup.size>0) {
                    nodeGroup[0].add(node)
                } else {
                    nodeGroups.add(mutableSetOf(node))
                }
            }
        }

        // create summary nodes
        val summaryNodes = mutableSetOf<SummaryNode<S, A>>()
        for (nodeGroup in nodeGroups) {
            summaryNodes.add(SummaryNode.create(nodeGroup))
        }
        val initSummaryNodes = summaryNodes.filter { summaryNode -> argTraces.get(0).node(0) in summaryNode.argNodes }
        checkState(initSummaryNodes.size==1, "Initial arg node must be in exactly 1 summary node!")
        val initNode = initSummaryNodes.get(0)

        // save edges as well, so we can easily connect edge sources and targets
        val summaryEdges = mutableSetOf<SummaryEdge<S, A>>()

        val inEdgeMap = mutableMapOf<ArgEdge<S, A>, SummaryNode<S, A>>()
        for(summaryNode in summaryNodes) {
            for(edge in summaryNode.getInEdges()) {
                checkState(!inEdgeMap.containsKey(edge))
                inEdgeMap[edge] = summaryNode
            }
        }
        for(summaryNode in summaryNodes) {
            val nodeOutEdges = summaryNode.getOutEdges()
            for(nodeOutEdge in nodeOutEdges) {
                if(inEdgeMap.containsKey(nodeOutEdge)) {
                    val targetSummaryNode = inEdgeMap[nodeOutEdge]!!
                    summaryEdges.add(SummaryEdge(nodeOutEdge, summaryNode, targetSummaryNode))
                }
            }
        }
        return AbstractTraceSummary(argTraces, summaryNodes, summaryEdges, initNode)
    }
}

/**
 * This class represents an automata, similar to an ARG, where covered and covering nodes
 * are merged into a single node (which we thus call a summary node).
 * In some sense this class represents a wrapper level over a set of arg traces.
 */
data class AbstractTraceSummary<S : State, A : Action> (
    val sourceTraces : Collection<ArgTrace<S, A>>,
    val summaryNodes : Collection<SummaryNode<S, A>>,
    val summaryEdges : Collection<SummaryEdge<S, A>>,
    val initNode : SummaryNode<S, A>
    ) : Witness {
}

/**
 * Groups arg nodes based on coverages, but also stores the traces they appear in, coverage relations and arg nodes
 */
class SummaryNode<S : State, A: Action> private constructor (val nodeSummaryId: Long, val argNodes: Set<ArgNode<S, A>>) {
    companion object {
        var counter : Long = 0

        fun <S : State, A : Action> create(argNodes: MutableSet<ArgNode<S, A>>) : SummaryNode<S, A> {
            // all of the nodes should be in some kind of coverage relationship with each other
            var leastOverApproximatedNode : ArgNode<S, A>
            var mostOverApproximatedNode : ArgNode<S, A>

            val notCoveringNodes = argNodes.filter { argNode -> argNode.coveredNodes.count() == 0L }
            for(node in notCoveringNodes) {
                for(node2 in notCoveringNodes) {
                    TODO() // see comment below - we want to find least over-approximated node
                }
            }

            /*
            public boolean mayCover(final ArgNode<S, A> node) {
                if (arg.getPartialOrd().isLeq(node.getState(), this.getState())) {
                    return ancestors().noneMatch(n -> n.equals(node) || n.isSubsumed());
                } else {
                    return false;
                }
            }

            public boolean mayCoverStandard(final ArgNode<S, A> node) {
                if (arg.getPartialOrd().isLeq(node.getState(), this.getState())) {
                    return !(this.equals(node) || this.isSubsumed()); // no need to check ancestors in CEGAR
                } else {
                    return false;
                }
            }

            * */

            return SummaryNode(counter++, argNodes)
        }
    }

    fun getOutEdges(): Set<ArgEdge<S, A>> {
        return argNodes.map { node -> node.outEdges.toList() }.flatten().toSet()
    }

    fun getInEdges() : Set<ArgEdge<S, A>> {
        return argNodes
            .filter { node -> node.inEdge.isPresent }
            .map { node -> node.inEdge.get() }.toSet()
    }

    fun getStates() : Set<S> {
        return argNodes.map { argNode -> argNode.state }.toSet()
    }

    fun getLabel() : String {
        val sb = StringBuilder()

        for (node in argNodes) {
            val label = node.state.toString()
            if(label !in sb) {
                sb.append(label)
            }
        }

        return sb.toString()
    }

    override fun toString(): String {
        return getLabel()
    }
}

data class SummaryEdge<S : State, A: Action>(
    val argEdge: ArgEdge<S, A>,
    val source: SummaryNode<S, A>,
    val target: SummaryNode<S, A>
) {
    fun getLabel() : String {
        return argEdge.action.toString()
    }
}