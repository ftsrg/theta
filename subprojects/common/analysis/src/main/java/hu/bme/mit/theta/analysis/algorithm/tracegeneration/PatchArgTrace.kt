package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace

/**
 * Traces built on ArgTraces, but capable of handling traces going through covered nodes
 */
class PatchArgTrace<S : State, A : Action> private constructor(val traces : List<ArgTrace<S, A>>) :
    Iterable<ArgNode<S, A>?> {
    private val nodes : List<ArgNode<S, A>> = traces.flatten()

    override fun iterator(): Iterator<ArgNode<S, A>?> {
        return nodes.iterator()
    }

    companion object {
        fun <S : State, A : Action> create(traces : List<ArgTrace<S, A>>) : PatchArgTrace<S, A> {

            return PatchArgTrace<S, A>(traces)
        }
    }
}
