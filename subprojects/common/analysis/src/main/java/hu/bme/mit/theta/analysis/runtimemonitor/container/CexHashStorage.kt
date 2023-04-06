package hu.bme.mit.theta.analysis.runtimemonitor.container

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgTrace

class CexHashStorage<S : State?, A : Action?> :
    RuntimeDataCollection<ArgTrace<S, A>?> {
    private val counterexamples: MutableSet<Int> = LinkedHashSet()
    override fun addData(newData: ArgTrace<S, A>?) {
        counterexamples.add(newData.hashCode())
    }

    override operator fun contains(data: ArgTrace<S, A>?): Boolean {
        return counterexamples.contains(data.hashCode())
    }
}