package hu.bme.mit.theta.analysis.runtimemonitor.container

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.common.Tuple2
import java.util.*
import kotlin.collections.LinkedHashSet

class ArgPrecHashStorage<S : State?, A : Action?, P : Prec?> :
    RuntimeDataCollection<Tuple2<ARG<S, A>?, P>> {
    private val argPrecPairs: MutableSet<Int> = LinkedHashSet()
    override fun addData(newData : Tuple2<ARG<S, A>?, P>) {
        argPrecPairs.add(hashArgPrec(newData))
    }

    override operator fun contains(data : Tuple2<ARG<S, A>?, P>): Boolean {
        return argPrecPairs.contains(hashArgPrec(data))
    }

    fun isEmpty() : Boolean {
        return argPrecPairs.isEmpty()
    }

    private fun hashArgPrec(newData: Tuple2<ARG<S, A>?, P>): Int {
        val arg = newData.get1()
        val prec = newData.get2()
        val argStates = arg!!.nodes.map(ArgNode<*, *>::getState).toList()
        val argInEdges = arg.nodes.map(ArgNode<*, *>::getInEdge).toList()
        return Objects.hash(argStates, argInEdges, prec)
    }
}