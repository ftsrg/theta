package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.Witness
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace
import hu.bme.mit.theta.analysis.utils.TraceSummaryVisualizer

class TraceGenerationSummaryBuilder<S : State, A : Action> {
    val argTraces: MutableList<ArgTrace<S, A>> = mutableListOf()

    fun addTrace(trace: ArgTrace<S, A>) {
        argTraces.add(trace)
    }

    fun build(): TraceSetSummary<S, A> {
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

        // create state summaries
        val summaryNodes = mutableSetOf<SummaryNode<S, A>>()
        for (nodeGroup in nodeGroups) {
            summaryNodes.add(SummaryNode.create(nodeGroup))
        }

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
        return TraceSetSummary(argTraces, summaryNodes, summaryEdges)
    }
}

/**
 * This class represents an automata, similar to an ARG, where covered and covering nodes
 * are merged into a single node (which we thus call a summary node).
 * In some sense this class represents a wrapper level over a set of arg traces.
 */
data class TraceSetSummary<S : State, A : Action> (
    val sourceTraces : Collection<ArgTrace<S, A>>,
    val summaryNodes : Collection<SummaryNode<S, A>>,
    val summaryEdges : Collection<SummaryEdge<S, A>>
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
            for(node in argNodes) {
                for (node2 in argNodes) {
                    checkState(
                        (node == node2) ||
                        (node.coveringNode.isPresent() && node.coveringNode.get() == node2) ||
                        (node.coveredNodes.anyMatch { n -> n==node2 })
                    )
                }
            }

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