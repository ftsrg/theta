/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.WrapperState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.model.AtomicFenceLabel.Companion.ATOMIC_MUTEX
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.util.*

private var pidCnt = 1
private var procCnt = 1

data class XcfaState<S : ExprState>
@JvmOverloads
constructor(
  val xcfa: XCFA?,
  val processes: Map<Int, XcfaProcessState>,
  val sGlobal: S,
  val mutexState: MutexState = MutexState(),
  val threadLookup: Map<VarDecl<*>, Int> = emptyMap(),
  val bottom: Boolean = false,
) : ExprState, WrapperState {

  constructor(
    xcfa: XCFA,
    loc: XcfaLocation,
    state: S,
  ) : this(
    xcfa = xcfa,
    processes =
      mapOf(0 to XcfaProcessState(locs = LinkedList(listOf(loc)), varLookup = LinkedList())),
    sGlobal = state,
  )

  val mutexes: Map<MutexLock, Map<Int, Int>>
    get() = mutexState.mutexes

  override fun isBottom(): Boolean {
    return bottom || sGlobal.isBottom
  }

  override fun toExpr(): Expr<BoolType> {
    return sGlobal.toExpr()
  }

  override fun getWrappedState(): S = sGlobal

  internal fun apply(a: XcfaAction): XcfaState<S> {
    val changes: MutableList<(XcfaState<S>) -> XcfaState<S>> = ArrayList()
    if (mutexes[ATOMIC_MUTEX]?.keys?.any { it != a.pid } == true) {
      return copy(bottom = true)
    }

    val processState = processes[a.pid]
    checkNotNull(processState)
    check(processState.locs.peek() == a.source)
    val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
    newProcesses[a.pid] = processes[a.pid]!!.withNewLoc(a.target)
    if (processes != newProcesses) {
      changes.add { state -> state.withProcesses(newProcesses) }
    }

    a.edge.getFlatLabels().forEach { label ->
      when (label) {
        is FenceLabel -> {
          when (label) {
            is AtomicBeginLabel,
            is MutexLockLabel,
            is RWLockReadLockLabel,
            is RWLockWriteLockLabel -> changes.add { it.enterMutex(label, a.pid) }

            is AtomicEndLabel,
            is MutexUnlockLabel,
            is RWLockUnlockLabel -> changes.add { it.exitMutex(label, a.pid) }

            is MutexTryLockLabel -> {
              check(label.successful != null) {
                "MutexTryLockLabel success must be encoded by the LTS."
              }
              changes.add { state ->
                val newState = state.enterMutex(label, a.pid)
                when {
                  newState.isBottom == label.successful -> state.copy(bottom = true) // disabled
                  newState.isBottom -> state // mutex lock did not succeed
                  else -> newState // mutex lock succeeded
                }
              }
            }
          }
        }

        is InvokeLabel -> {
          if (label.isLibraryFunction) {
            changes.add { state ->
              state.copy(mutexState = state.mutexState.apply(label, state.sGlobal))
            }
            return@forEach
          }
          val proc =
            xcfa?.procedures?.find { proc -> proc.name == label.name }
              ?: error("No such method ${label.name}.")
          val returnStmt =
            SequenceLabel(
              proc.params
                .withIndex()
                .filter { it.value.second != ParamDirection.IN }
                .map { iVal ->
                  AssignStmtLabel(
                    label.params[iVal.index] as RefExpr<*>,
                    cast(iVal.value.first.ref, iVal.value.first.type),
                    metadata = label.metadata,
                  )
                }
            )
          changes.add { state ->
            state.invokeFunction(a.pid, proc, returnStmt, proc.params.toMap(), label.tempLookup)
          }
        }

        is ReturnLabel -> changes.add { state -> state.returnFromFunction(a.pid) }

        is StartLabel -> changes.add { state -> state.start(label, a.pid) }
        is JoinLabel -> {
          changes.add { state ->
            // joining a thread that was never started is a no-op (there is nothing to wait
            // for); only block while a started thread is still running
            val joinedPid = state.threadLookup[label.pidVar]
            if (joinedPid != null && joinedPid in state.processes) copy(bottom = true) else state
          }
        }

        else -> {}
      }
    }

    changes.add { state ->
      if (state.processes[a.pid]!!.locs.isEmpty()) state.endProcess(a.pid) else state
    }

    return changes.fold(this) { current, change -> change(current) }
  }

  private fun start(startLabel: StartLabel, startingPid: Int): XcfaState<S> {
    val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
    val newThreadLookup: MutableMap<VarDecl<*>, Int> = LinkedHashMap(threadLookup)

    val procedure = xcfa?.procedures?.find { it.name == startLabel.name }!!
    val paramList = procedure.params.toMap()
    val tempLookup = startLabel.tempLookup
    val returnStmt =
      SequenceLabel(
        emptyList() // TODO: return values are handled in JoinLabel instead -- how to solve this?
        //            procedure.params.withIndex().filter { it.value.second != ParamDirection.IN }
        //                .map { iVal ->
        //                    StmtLabel(Assign(
        //                        cast((startLabel.params[iVal.index] as RefExpr<*>).decl as
        // VarDecl<*>,
        //                            iVal.value.first.type),
        //                        cast(iVal.value.first.ref, iVal.value.first.type)),
        //                        metadata = startLabel.metadata)
        //                }
      )

    val pid = pidCnt++
    val lookup = procedure.createLookup("T$pid")
    newThreadLookup[startLabel.pidVar] = pid
    newProcesses[pid] =
      XcfaProcessState(
        LinkedList(listOf(procedure.initLoc)),
        prefix = "T$pid",
        varLookup = LinkedList(listOf(lookup)),
        returnStmts = LinkedList(listOf(returnStmt)),
        paramStmts =
          LinkedList(
            listOf(
              Pair(
                /* init */
                SequenceLabel(
                  paramList
                    .filter { it.value != ParamDirection.OUT }
                    .map {
                      StmtLabel(
                        Assign(
                          cast(it.key.changeVars(lookup), it.key.type),
                          cast(it.key.changeVars(tempLookup).ref, it.key.type),
                        )
                      )
                    }
                ),
                /* deinit */
                SequenceLabel(
                  paramList
                    .filter { it.value != ParamDirection.IN }
                    .map {
                      StmtLabel(
                        Assign(
                          cast(it.key.changeVars(tempLookup), it.key.type),
                          cast(it.key.changeVars(lookup).ref, it.key.type),
                        )
                      )
                    }
                ),
              )
            )
          ),
      )

    newProcesses[startingPid] =
      newProcesses[startingPid]!!.let {
        it.copy(invokeParameterCounter = it.invokeParameterCounter + 1)
      }

    return copy(processes = newProcesses, threadLookup = newThreadLookup)
  }

  private fun endProcess(pid: Int): XcfaState<S> {
    val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
    newProcesses.remove(pid)
    return copy(processes = newProcesses)
  }

  private fun invokeFunction(
    pid: Int,
    proc: XcfaProcedure,
    returnStmt: XcfaLabel,
    paramList: Map<VarDecl<*>, ParamDirection>,
    tempLookup: Map<VarDecl<*>, VarDecl<*>>,
  ): XcfaState<S> {
    val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
    newProcesses[pid] = processes[pid]?.enterFunction(proc, returnStmt, paramList, tempLookup)!!
    return copy(processes = newProcesses)
  }

  private fun returnFromFunction(pid: Int): XcfaState<S> {
    val newProcesses: MutableMap<Int, XcfaProcessState> = LinkedHashMap(processes)
    newProcesses[pid] = processes[pid]?.exitFunction()!!
    return copy(processes = newProcesses)
  }

  private fun enterMutex(label: FenceLabel, pid: Int): XcfaState<S> =
    mutexState.enter(label, pid, sGlobal)?.let { copy(mutexState = it) } ?: copy(bottom = true)

  private fun exitMutex(label: FenceLabel, pid: Int): XcfaState<S> =
    copy(mutexState = mutexState.exit(label, pid, sGlobal))

  private fun withProcesses(nP: Map<Int, XcfaProcessState>): XcfaState<S> {
    return copy(processes = nP)
  }

  fun withLocation(pid: Int, loc: XcfaLocation): XcfaState<S> {
    val nP = processes.toMutableMap()
    nP[pid] =
      nP[pid]?.withNewLoc(loc) ?: XcfaProcessState(locs = LinkedList(listOf(loc)), LinkedList())
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
  val paramStmts: LinkedList<Pair<XcfaLabel, XcfaLabel>> =
    LinkedList(listOf(Pair(NopLabel, NopLabel))),
  val paramsInitialized: Boolean = false,
  val prefix: String = "",
  val invokeParameterCounter: Int = 0,
) {

  internal var popped: XcfaLocation? =
    null // stores if the stack was popped due to abstract stack covering

  fun withNewLoc(l: XcfaLocation): XcfaProcessState {
    val deque: LinkedList<XcfaLocation> = LinkedList(locs)
    deque.pop()
    deque.push(l)
    return copy(locs = deque, paramsInitialized = true)
  }

  override fun toString(): String =
    when (locs.size) {
      0 -> ""
      1 -> locs.peek()!!.toString() + " initialized=$paramsInitialized"
      else -> "${locs.peek()!!} [${locs.size}], initilized=$paramsInitialized"
    }

  fun enterFunction(
    xcfaProcedure: XcfaProcedure,
    returnStmt: XcfaLabel,
    paramList: Map<VarDecl<*>, ParamDirection>,
    tempLookup: Map<VarDecl<*>, VarDecl<*>>,
  ): XcfaProcessState {
    val deque: LinkedList<XcfaLocation> = LinkedList(locs)
    val varLookup: LinkedList<Map<VarDecl<*>, VarDecl<*>>> = LinkedList(varLookup)
    val returnStmts: LinkedList<XcfaLabel> = LinkedList(returnStmts)
    val paramStmts: LinkedList<Pair<XcfaLabel, XcfaLabel>> = LinkedList(paramStmts)
    deque.push(xcfaProcedure.initLoc)
    val lookup = xcfaProcedure.createLookup(prefix, "P${procCnt++}")
    varLookup.push(lookup)
    returnStmts.push(returnStmt)
    paramStmts.push(
      Pair(
        /* init */
        SequenceLabel(
          paramList
            .filter { it.value != ParamDirection.OUT }
            .map {
              StmtLabel(
                Assign(
                  cast(it.key.changeVars(lookup), it.key.type),
                  cast(it.key.changeVars(tempLookup).ref, it.key.type),
                )
              )
            }
        ),
        /* deinit */
        SequenceLabel(
          paramList
            .filter { it.value != ParamDirection.IN }
            .map {
              StmtLabel(
                Assign(
                  cast(it.key.changeVars(tempLookup), it.key.type),
                  cast(it.key.changeVars(lookup).ref, it.key.type),
                )
              )
            }
        ),
      )
    )
    return copy(
      locs = deque,
      varLookup = varLookup,
      returnStmts = returnStmts,
      paramStmts = paramStmts,
      paramsInitialized = false,
      invokeParameterCounter = invokeParameterCounter + 1,
    )
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
    return copy(
      locs = deque,
      varLookup = varLookup,
      returnStmts = returnStmts,
      paramStmts = paramStmts,
    )
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
    result = 31 * result + paramsInitialized.hashCode()
    return result
  }

  companion object {

    fun XcfaProcedure.createLookup(
      threadPrefix: String = "",
      procPrefix: String = "",
    ): Map<VarDecl<*>, VarDecl<*>> =
      listOf(params.map { it.first }, vars)
        .flatten()
        .associateWith {
          val sj = StringJoiner("::")
          if (threadPrefix != "") sj.add(threadPrefix) else sj.add("_")
          if (procPrefix != "") sj.add(procPrefix) else sj.add("_")
          sj.add(it.name)
          val name = sj.toString()
          if (name != it.name) Var(sj.toString(), it.type) else it
        }
        .filter { it.key != it.value }
  }
}

operator fun Regex.contains(text: CharSequence): Boolean = this.matches(text)
