/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.*

data class XcfaState<S : ExprState>(
        val processes: Map<Int, XcfaProcessState>,
        val sGlobal: S
): ExprState {
    override fun isBottom(): Boolean {
        return sGlobal.isBottom
    }

    override fun toExpr(): Expr<BoolType> {
        return sGlobal.toExpr()
    }

    fun applyLoc(a: XcfaAction) : XcfaState<S>{
        val processState = processes[a.pid]
        checkNotNull(processState)
        check(processState.locs.peek() == a.source)
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap()
        for ((i, st) in processes) {
            if(i == a.pid) newProcesses[i] = st.withNewLoc(a.target)
            else newProcesses[i] = st
        }
        return XcfaState(newProcesses, sGlobal)
    }

    fun withState(s: S): XcfaState<S> {
        return XcfaState(processes, s)
    }

    override fun toString(): String {
        return "$processes {$sGlobal}"
    }
}

data class XcfaProcessState(
        val locs: LinkedList<XcfaLocation>
) {
    fun withNewLoc(l: XcfaLocation) : XcfaProcessState {
        val deque: LinkedList<XcfaLocation> = LinkedList(locs)
        deque.pop()
        deque.push(l)
        return XcfaProcessState(deque)
    }

    override fun toString(): String = when(locs.size) {
        0 -> ""
        1 -> locs.peek()!!.toString()
        else -> "${locs.peek()!!} [${locs.size}]"
    }
}