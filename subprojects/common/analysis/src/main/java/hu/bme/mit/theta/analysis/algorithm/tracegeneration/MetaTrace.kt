package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import java.util.*

data class StateMetadata<S : State>(val state: S, val id: Int, val coveringNodeId: Optional<Int>)

class MetaTrace<S : State>(nodes: List<ArgNode<S, *>>) {
    val stateMetadata: Map<Int, StateMetadata<S>> = nodes.associateBy(
        keySelector = { it.id },
        valueTransform = { node ->
            val state = node.state
            val id = node.id
            if (node.coveringNode.isPresent) {
                val coveringNodeId = node.coveringNode.get().id
                StateMetadata(state, id, Optional.of(coveringNodeId))
            }
            else {
                StateMetadata(state, id, Optional.empty())
            }
        }
    )
}
