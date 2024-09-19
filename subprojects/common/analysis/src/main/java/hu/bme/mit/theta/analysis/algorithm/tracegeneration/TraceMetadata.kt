package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace

class TraceGenerationMetadataBuilder<S : State, A : Action> {

    val argTraces: MutableList<ArgTrace<S, A>> = mutableListOf()

    fun addTrace(trace: ArgTrace<S, A>) {
        argTraces.add(trace)
    }

    fun build(): Collection<TraceMetadata<S, A>> {
        // first create the meta traces and states
        val metadataTraces = mutableMapOf<ArgTrace<S, A>, TraceMetadata<S, A>>()
        val metadataStates = mutableMapOf<Pair<ArgTrace<S, A>, ArgNode<S, A>>, StateMetadata<S, A>>()

        for (argTrace in argTraces) {
            val states: MutableSet<StateMetadata<S, A>> = mutableSetOf()
            for (argNode in argTrace) {
                val state = StateMetadata<S, A>(argNode.state)
                metadataStates[Pair(argTrace, argNode)] = state
                states.add(state)
            }
            val traceMetadata = TraceMetadata.create(states)
            metadataTraces[argTrace] = traceMetadata
        }

        collectCoverStates(metadataTraces, metadataStates)

        print(metadataTraces.values)
        return metadataTraces.values
    }

    private fun collectCoverStates(
        metadataTraces: Map<ArgTrace<S, A>, TraceMetadata<S, A>>,
        metadataStates: Map<Pair<ArgTrace<S, A>, ArgNode<S, A>>, StateMetadata<S, A>>)
    {
        // connect the meta states based on coverages.
        // must be done after creation of all meta states,
        // so that they can reference each other
        for (entry in metadataStates) {
            val node = entry.key.second
            val state = entry.value

            node.coveredNodes.forEach { coveredNode ->
                metadataTraces.keys.forEach { trace ->
                    metadataStates[Pair(trace, coveredNode)]?.let { coveredMetaState ->
                        if (coveredMetaState != state) {
                            coveredMetaState.coveringState.add(state)
                        }
                    }
                }
            }

            node.coveringNode.get().let { coveringNode ->
                metadataTraces.keys.forEach { trace ->
                    metadataStates[Pair(trace, coveringNode)]?.let { coveredMetaState ->
                        if (coveredMetaState != state) {
                            coveredMetaState.coveringState.add(state)
                        }
                    }
                }
            }
        }
    }
}

/**
 * Represents the metadata for a set of traces generated from an ARG
 * The goal here is to have unique identifier for each trace and each state in each trace
 * Also, coverage information (even though we don't have ArgNode-s here)
 */
class TraceMetadata<S : State, A : Action> private constructor(val id : Long, val states : Set<StateMetadata<S,A>>) {
    companion object {
        var counter : Long = 0

        fun <S : State, A : Action> create(states : Set<StateMetadata<S,A>>)
        : TraceMetadata<S, A> {
            val traceMetadata = TraceMetadata(counter, states)
            counter++
            return traceMetadata
        }
    }

    override fun toString(): String {
        val sb = StringBuilder()
        sb.append("T$id{")
        sb.append("states: $states")
        sb.append("}")
        return sb.toString()
    }
}

/**
 * We want to differentiate states based on the trace they are in
 */
class StateMetadata<S : State, A: Action> (val state: State, val id : Long = counter++) {
    val coveringState: MutableSet<StateMetadata<S, A>> = mutableSetOf() // TODO()
    val coveredState: MutableSet<StateMetadata<S, A>> = mutableSetOf() // TODO()

    companion object {
        var counter : Long = 0
    }

    override fun toString(): String {
        return "S$id"
    }
}

fun <S : State, A : Action> ArgNode<S, A>.getStateMetadata() {
    for(coveringNodes in this.coveredNodes) {
        coveringNodes
    }
    this.coveringNode
}