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
    override fun addData(newData: Tuple2<ARG<S, A>?, P>) {
        argPrecPairs.add(hashArgPrec(newData))
    }

    override operator fun contains(data: Tuple2<ARG<S, A>?, P>): Boolean {
        return argPrecPairs.contains(hashArgPrec(data))
    }

    fun isEmpty(): Boolean {
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