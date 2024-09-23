package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace

sealed class TraceGenerationSummaryBuilder<S : State, A : Action> {
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

                checkState(nodeGroup.size == 1)

                nodeGroup[0].add(node)
            }
        }

        // create state summaries
        val nodeSummaries = mutableSetOf<NodeSummary<S, A>>()
        for (nodeGroup in nodeGroups) {
            nodeSummaries.add(NodeSummary.create(nodeGroup))
        }

        return TraceSetSummary<S, A>(argTraces, nodeSummaries)
    }
}

data class TraceSetSummary<S : State, A : Action> constructor(
    val sourceTraces : Collection<ArgTrace<S, A>>,
    val stateSummaries : Collection<NodeSummary<S, A>>,
    ) {

    override fun toString(): String {
        TODO()
    }
}

/**
 * Groups arg nodes based on coverages, but also stores the traces they appear in, coverage relations and arg nodes
 */
class NodeSummary<S : State, A: Action> private constructor (val nodeSummaryId: Long, val argNodes: Set<ArgNode<S, A>>) {
    companion object {
        var counter : Long = 0

        fun <S : State, A : Action> create(argNodes: MutableSet<ArgNode<S, A>>) : NodeSummary<S, A> {
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

            return NodeSummary(counter++, argNodes)
        }
    }

    fun getOutEdges() {
        TODO()
    }

    fun getInEdges() {
        TODO()
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