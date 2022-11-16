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
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.util.*

data class XcfaState<S : ExprState> @JvmOverloads constructor(
        val xcfa: XCFA?, // TODO: remove this
        val processes: Map<Int, XcfaProcessState>,
        val sGlobal: S,
        val mutexes: Map<String, Int> = processes.keys.associateBy { "$it" },
        val threadLookup: Map<VarDecl<*>, Int> = emptyMap(),
        val bottom: Boolean = false,
): ExprState {
    override fun isBottom(): Boolean {
        return bottom || sGlobal.isBottom
    }

    override fun toExpr(): Expr<BoolType> {
        return sGlobal.toExpr()
    }

    fun apply(a: XcfaAction) : Pair<XcfaState<S>, XcfaAction>{
        val changes: MutableList<(XcfaState<S>) -> XcfaState<S>> = ArrayList()
        if(mutexes[""] != null && mutexes[""] != a.pid) return Pair(copy(bottom=true), a.withLabel(SequenceLabel(listOf(NopLabel))))

        val processState = processes[a.pid]
        checkNotNull(processState)
        check(processState.locs.peek() == a.source)
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        newProcesses[a.pid] = checkNotNull(processes[a.pid]?.withNewLoc(a.target))
        if(processes != newProcesses) {
            changes.add { state -> state.withProcesses(newProcesses) }
        }


        val newLabels = a.edge.getFlatLabels().filter {
            when(it) {
                is FenceLabel -> it.labels.forEach { label ->
                    when(label) {
                        "ATOMIC_BEGIN" -> changes.add { it.enterMutex("", a.pid) }
                        "ATOMIC_END" -> changes.add { it.exitMutex("", a.pid) }
                        in Regex("mutex_lock\\((.*)\\)") -> changes.add { state -> state.enterMutex( label.substring("mutex_lock".length + 1, label.length-1), a.pid)}
                        in Regex("mutex_unlock\\((.*)\\)") -> changes.add { state -> state.exitMutex( label.substring("mutex_unlock".length + 1, label.length-1), a.pid )}
                    }
                }.let { false }
                is InvokeLabel -> error("Function invocations not yet supported")
                is JoinLabel -> {
                    changes.add { state -> state.enterMutex(it.pidVar.name, a.pid) }
                    changes.add { state -> state.exitMutex(it.pidVar.name, a.pid) }
                }
                is NondetLabel -> true
                NopLabel -> false
                is ReadLabel -> error("Read/Write labels not yet supported")
                is SequenceLabel -> true
                is StartLabel ->  changes.add { state -> state.start(it) }.let { false }
                is StmtLabel -> true
                is WriteLabel -> error("Read/Write labels not yet supported")
            }
        }

        if(a.target.final) {
            if(checkNotNull(newProcesses[a.pid]).locs.size == 1) {
                changes.add { state -> state.endProcess(a.pid) }
            }
        }

        return Pair(changes.fold(this) { current, change -> change(current) }, a.withLabel(SequenceLabel(newLabels)))
    }

    private fun start(startLabel: StartLabel): XcfaState<S> {
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)

        val procedure = checkNotNull(xcfa?.procedures?.find { it.name == startLabel.name })

        val pid = newProcesses.size
        newProcesses[pid] = XcfaProcessState(LinkedList(listOf(procedure.initLoc)), LinkedList(listOf(procedure.vars.associateWith { Var("T${pid}::${it.name}", it.type)  })))
        val newMutexes = LinkedHashMap(mutexes)
        newMutexes["$pid"] = pid

        return copy(processes=newProcesses, mutexes=newMutexes)
    }

    private fun endProcess(pid: Int): XcfaState<S> {
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        newProcesses.remove(pid)
        val newMutexes = LinkedHashMap(mutexes)
        newMutexes.remove("$pid")
        return copy(processes=newProcesses)
    }

    fun enterMutex(key: String, pid: Int): XcfaState<S> {
        if(mutexes.keys.any { it == key && mutexes[it] != pid }) return copy(bottom = true)

        val newMutexes = LinkedHashMap(mutexes)
        newMutexes[key] = pid
        return copy(mutexes = newMutexes)
    }

    fun exitMutex(key: String, pid: Int): XcfaState<S> {
        val newMutexes = LinkedHashMap(mutexes)
        newMutexes.remove(key, pid)
        return copy(mutexes = newMutexes)
    }


    private fun withProcesses(nP: Map<Int, XcfaProcessState>): XcfaState<S> {
        return copy(processes=nP)
    }

    fun withState(s: S): XcfaState<S> {
        return copy(sGlobal=s)
    }

    override fun toString(): String {
        return "$processes {$sGlobal}"
    }
}

data class XcfaProcessState(
        val locs: LinkedList<XcfaLocation>,
        val varLookup: LinkedList<Map<VarDecl<*>, VarDecl<*>>> = LinkedList(listOf(emptyMap()))
) {
    fun withNewLoc(l: XcfaLocation) : XcfaProcessState {
        val deque: LinkedList<XcfaLocation> = LinkedList(locs)
        deque.pop()
        deque.push(l)
        return copy(locs = deque)
    }

    override fun toString(): String = when(locs.size) {
        0 -> ""
        1 -> locs.peek()!!.toString()
        else -> "${locs.peek()!!} [${locs.size}]"
    }
}

operator fun Regex.contains(text: CharSequence): Boolean = this.matches(text)
