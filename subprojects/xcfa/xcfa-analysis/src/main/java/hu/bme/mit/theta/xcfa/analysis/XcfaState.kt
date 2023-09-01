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

package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.changeVars
import java.util.*

private var pidCnt = 1
private var procCnt = 1

data class XcfaState<S : ExprState> @JvmOverloads constructor(
    val xcfa: XCFA?,
    val processes: Map<Int, XcfaProcessState>,
    val sGlobal: S,
    val mutexes: Map<String, Int> = processes.keys.associateBy { "$it" },
    val threadLookup: Map<VarDecl<*>, Int> = emptyMap(),
    val bottom: Boolean = false,
) : ExprState {


    override fun isBottom(): Boolean {
        return bottom || sGlobal.isBottom
    }

    override fun toExpr(): Expr<BoolType> {
        return sGlobal.toExpr()
    }

    fun apply(a: XcfaAction): Pair<XcfaState<S>, XcfaAction> {
        val changes: MutableList<(XcfaState<S>) -> XcfaState<S>> = ArrayList()
        if (mutexes[""] != null && mutexes[""] != a.pid) return Pair(copy(bottom = true),
            a.withLabel(SequenceLabel(listOf(NopLabel))))

        val processState = processes[a.pid]
        checkNotNull(processState)
        check(processState.locs.peek() == a.source)
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        newProcesses[a.pid] = checkNotNull(processes[a.pid]?.withNewLoc(a.target))
        if (processes != newProcesses) {
            changes.add { state -> state.withProcesses(newProcesses) }
        }

        val newLabels = a.edge.getFlatLabels().filter {
            when (it) {
                is FenceLabel -> it.labels.forEach { label ->
                    when (label) {
                        "ATOMIC_BEGIN" -> changes.add { it.enterMutex("", a.pid) }
                        "ATOMIC_END" -> changes.add { it.exitMutex("", a.pid) }
                        in Regex("mutex_lock\\((.*)\\)") -> changes.add { state ->
                            state.enterMutex(
                                label.substring("mutex_lock".length + 1, label.length - 1), a.pid)
                        }

                        in Regex("mutex_unlock\\((.*)\\)") -> changes.add { state ->
                            state.exitMutex(
                                label.substring("mutex_unlock".length + 1, label.length - 1), a.pid)
                        }
                    }
                }.let { false }

                is InvokeLabel -> {
                    val proc = xcfa?.procedures?.find { proc -> proc.name == it.name } ?: error(
                        "No such method ${it.name}.")
                    val returnStmt = SequenceLabel(
                        proc.params.withIndex().filter { it.value.second != ParamDirection.IN }
                            .map { iVal ->
                                StmtLabel(Assign(
                                    cast((it.params[iVal.index] as RefExpr<*>).decl as VarDecl<*>,
                                        iVal.value.first.type),
                                    cast(iVal.value.first.ref, iVal.value.first.type)),
                                    metadata = it.metadata)
                            })
                    changes.add { state ->
                        state.invokeFunction(a.pid, proc, returnStmt, proc.params.toMap(),
                            it.tempLookup)
                    }
                    false
                }

                is ReturnLabel -> changes.add { state -> state.returnFromFunction(a.pid) }
                    .let { true }

                is JoinLabel -> {
                    changes.add { state -> state.enterMutex("${threadLookup[it.pidVar]}", a.pid) }
                    changes.add { state -> state.exitMutex("${threadLookup[it.pidVar]}", a.pid) }
                    false
                }

                is NondetLabel -> true
                NopLabel -> false
                is ReadLabel -> error("Read/Write labels not yet supported")
                is SequenceLabel -> true
                is StartLabel -> changes.add { state -> state.start(it) }.let { true }
                is StmtLabel -> true
                is WriteLabel -> error("Read/Write labels not yet supported")
            }
        }

        changes.add { state ->
            if (checkNotNull(state.processes[a.pid]).locs.isEmpty()) state.endProcess(
                a.pid) else state
        }

        return Pair(changes.fold(this) { current, change -> change(current) },
            a.withLabel(SequenceLabel(newLabels)))
    }

    private fun start(startLabel: StartLabel): XcfaState<S> {
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        val newThreadLookup: MutableMap<VarDecl<*>, Int> = LinkedHashMap(threadLookup)

        val procedure = checkNotNull(xcfa?.procedures?.find { it.name == startLabel.name })
        val paramList = procedure.params.toMap()
        val tempLookup = startLabel.tempLookup
        val returnStmt = SequenceLabel(
            emptyList() // TODO: return values are handled in JoinLabel instead -- how to solve this?
//            procedure.params.withIndex().filter { it.value.second != ParamDirection.IN }
//                .map { iVal ->
//                    StmtLabel(Assign(
//                        cast((startLabel.params[iVal.index] as RefExpr<*>).decl as VarDecl<*>,
//                            iVal.value.first.type),
//                        cast(iVal.value.first.ref, iVal.value.first.type)),
//                        metadata = startLabel.metadata)
//                }
        )

        val pid = pidCnt++
        val lookup = XcfaProcessState.createLookup(procedure, "T$pid", "")
        newThreadLookup[startLabel.pidVar] = pid
        newProcesses[pid] = XcfaProcessState(
            LinkedList(listOf(procedure.initLoc)),
            prefix = "T$pid",
            varLookup = LinkedList(listOf(lookup)),
            returnStmts = LinkedList(listOf(returnStmt)),
            paramStmts = LinkedList(listOf(Pair(
                /* init */
                SequenceLabel(paramList.filter { it.value != ParamDirection.OUT }.map {
                    StmtLabel(Assign(cast(it.key.changeVars(lookup), it.key.type),
                        cast(it.key.changeVars(tempLookup).ref, it.key.type)),
                        metadata = EmptyMetaData)
                }),
                /* deinit */
                SequenceLabel(paramList.filter { it.value != ParamDirection.IN }.map {
                    StmtLabel(Assign(cast(it.key.changeVars(tempLookup), it.key.type),
                        cast(it.key.changeVars(lookup).ref, it.key.type)), metadata = EmptyMetaData)
                }),
            ))))
        val newMutexes = LinkedHashMap(mutexes)
        newMutexes["$pid"] = pid

        return copy(processes = newProcesses, threadLookup = newThreadLookup, mutexes = newMutexes)
    }

    private fun endProcess(pid: Int): XcfaState<S> {
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        newProcesses.remove(pid)
        val newMutexes = LinkedHashMap(mutexes)
        newMutexes.remove("$pid")
        return copy(processes = newProcesses, mutexes = newMutexes)
    }

    private fun invokeFunction(pid: Int, proc: XcfaProcedure, returnStmt: XcfaLabel,
        paramList: Map<VarDecl<*>, ParamDirection>,
        tempLookup: Map<VarDecl<*>, VarDecl<*>>): XcfaState<S> {
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        newProcesses[pid] = checkNotNull(
            processes[pid]?.enterFunction(proc, returnStmt, paramList, tempLookup))
        return copy(processes = newProcesses)
    }

    private fun returnFromFunction(pid: Int): XcfaState<S> {
        val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
        newProcesses[pid] = checkNotNull(processes[pid]?.exitFunction())
        return copy(processes = newProcesses)
    }

    fun enterMutex(key: String, pid: Int): XcfaState<S> {
        if (mutexes.keys.any { it == key && mutexes[it] != pid }) return copy(bottom = true)

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
        return copy(processes = nP)
    }

    fun withState(s: S): XcfaState<S> {
        return copy(sGlobal = s)
    }

    override fun toString(): String {
        return "$processes {$sGlobal, mutex=$mutexes${if (bottom) ", bottom" else ""}}"
    }
}

data class XcfaProcessState(
    val locs: LinkedList<XcfaLocation>,
    val varLookup: LinkedList<Map<VarDecl<*>, VarDecl<*>>>,
    val returnStmts: LinkedList<XcfaLabel> = LinkedList(listOf(NopLabel)),
    val paramStmts: LinkedList<Pair<XcfaLabel, XcfaLabel>> = LinkedList(
        listOf(Pair(NopLabel, NopLabel))),
    val paramsInitialized: Boolean = false,
    val prefix: String = ""
) {

    fun withNewLoc(l: XcfaLocation): XcfaProcessState {
        val deque: LinkedList<XcfaLocation> = LinkedList(locs)
        deque.pop()
        deque.push(l)
        return copy(locs = deque, paramsInitialized = true)
    }

    override fun toString(): String = when (locs.size) {
        0 -> ""
        1 -> locs.peek()!!.toString() + " initialized=$paramsInitialized"
        else -> "${locs.peek()!!} [${locs.size}], initilized=$paramsInitialized"
    }

    fun enterFunction(xcfaProcedure: XcfaProcedure, returnStmt: XcfaLabel,
        paramList: Map<VarDecl<*>, ParamDirection>,
        tempLookup: Map<VarDecl<*>, VarDecl<*>>): XcfaProcessState {
        val deque: LinkedList<XcfaLocation> = LinkedList(locs)
        val varLookup: LinkedList<Map<VarDecl<*>, VarDecl<*>>> = LinkedList(varLookup)
        val returnStmts: LinkedList<XcfaLabel> = LinkedList(returnStmts)
        val paramStmts: LinkedList<Pair<XcfaLabel, XcfaLabel>> = LinkedList(paramStmts)
        deque.push(xcfaProcedure.initLoc)
        val lookup = createLookup(xcfaProcedure, prefix, "P${procCnt++}")
        varLookup.push(lookup)
        returnStmts.push(returnStmt)
        paramStmts.push(Pair(
            /* init */
            SequenceLabel(paramList.filter { it.value != ParamDirection.OUT }.map {
                StmtLabel(Assign(cast(it.key.changeVars(lookup), it.key.type),
                    cast(it.key.changeVars(tempLookup).ref, it.key.type)), metadata = EmptyMetaData)
            }),
            /* deinit */
            SequenceLabel(paramList.filter { it.value != ParamDirection.IN }.map {
                StmtLabel(Assign(cast(it.key.changeVars(tempLookup), it.key.type),
                    cast(it.key.changeVars(lookup).ref, it.key.type)), metadata = EmptyMetaData)
            }),
        ))
        return copy(locs = deque, varLookup = varLookup, returnStmts = returnStmts,
            paramStmts = paramStmts, paramsInitialized = false)
    }

    fun exitFunction(): XcfaProcessState {
        val deque: LinkedList<XcfaLocation> = LinkedList(locs)
        val varLookup: LinkedList<Map<VarDecl<*>, VarDecl<*>>> = LinkedList(varLookup)
        val returnStmts: LinkedList<XcfaLabel> = LinkedList(returnStmts)
        val paramStmts: LinkedList<Pair<XcfaLabel, XcfaLabel>> = LinkedList(paramStmts)
        deque.pop()
        varLookup.pop()
        returnStmts.pop()
        paramStmts.pop()
        return copy(locs = deque, varLookup = varLookup, returnStmts = returnStmts,
            paramStmts = paramStmts)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as XcfaProcessState

        if (locs != other.locs) return false
        if (paramsInitialized != other.paramsInitialized) return false

        return true
    }

    override fun hashCode(): Int {
        var result = locs.hashCode()
        result = 31 * result + paramsInitialized.hashCode() // TODO FRICKIN INNER STATE HASH
        return result
    }

    companion object {

        fun createLookup(proc: XcfaProcedure, threadPrefix: String,
            procPrefix: String): Map<VarDecl<*>, VarDecl<*>> =
            listOf(proc.params.map { it.first }, proc.vars).flatten().associateWith {
                val sj = StringJoiner("::")
                if (threadPrefix != "") sj.add(threadPrefix)
                else sj.add("_")
                if (procPrefix != "") sj.add(procPrefix)
                else sj.add("_")
                sj.add(it.name)
                val name = sj.toString()
                if (name != it.name) Var(sj.toString(), it.type)
                else it
            }.filter { it.key != it.value }
    }


}

operator fun Regex.contains(text: CharSequence): Boolean = this.matches(text)
