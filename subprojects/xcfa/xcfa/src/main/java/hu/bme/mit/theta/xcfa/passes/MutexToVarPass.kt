/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Replaces mutexes (except the atomic block mutexes) with counting variables.
 *
 * mutex_lock(mutex_var) -> assume(mutex_var = 0); mutex_var := mutex_var + 1; (atomically)
 *
 * mutex_unlock(mutex_var) -> mutex_var := mutex_var - 1;
 */
class MutexToVarPass : ProcedurePass {

  companion object {
    private val mutexVars = mutableMapOf<LitExpr<*>, VarDecl<IntType>>()

    private val LitExpr<*>.mutexFlag
      get() = mutexVars.getOrPut(this) { Decls.Var("__theta_mutex_flag_$this", Int()) }

    private val Expr<*>.mutexFlag
      get() = (this as? IntLitExpr)?.mutexFlag
        ?: throw UnsupportedOperationException("Unknown mutex not supported by mutex elimination.")
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      builder.removeEdge(edge)
      edge.label.replaceMutex().let { newLabels ->
        if (newLabels.isNotEmpty()) {
          newLabels.forEach { newLabel -> builder.addEdge(edge.withLabel(newLabel)) }
        } else {
          builder.addEdge(edge.withLabel(SequenceLabel(listOf())))
        }
      }
    }

    mutexVars.forEach { (_, v) -> builder.parent.addVar(XcfaGlobalVar(v, Int(0), atomic = true)) }
    builder.parent.getInitProcedures().forEach { (proc, _) ->
      mutexVars.forEach { (_, v) ->
        val initEdge = proc.initLoc.outgoingEdges.first()
        val initLabels = initEdge.getFlatLabels()
        if (
          initLabels.none { it is StmtLabel && it.stmt is AssignStmt<*> && it.stmt.varDecl == v }
        ) {
          val assign = StmtLabel(AssignStmt.of(v, Int(0)))
          val label = SequenceLabel(initLabels + assign, metadata = initEdge.label.metadata)
          proc.removeEdge(initEdge)
          proc.addEdge(initEdge.withLabel(label))
        }
      }
    }
    return builder
  }

  private fun XcfaLabel.replaceMutex(): Set<XcfaLabel> {
    return when (this) {
      is SequenceLabel ->
        descartes(labels.map { it.replaceMutex() }).map { SequenceLabel(it, metadata) }.toSet()

      is FenceLabel -> {
        val actions = mutableListOf<XcfaLabel>()

        when (this) {
          is AtomicFenceLabel -> actions.add(this)

          is RWLockUnlockLabel -> {
            // this is a hack because RWLockUnlock unlocks both read and write locks
            // if write lock is held, it unlocks that, otherwise a read lock
            val writeFlag = lock.mutexFlag
            val readFlag = lock.mutexFlag
            return setOf(
              SequenceLabel(
                listOf(
                  StmtLabel(AssumeStmt.of(Eq(writeFlag.ref, Int(0)))),
                  StmtLabel(AssignStmt.of(readFlag, Sub(readFlag.ref, Int(1)))),
                )
              ),
              SequenceLabel(
                listOf(
                  StmtLabel(AssumeStmt.of(Neq(writeFlag.ref, Int(0)))),
                  StmtLabel(AssignStmt.of(writeFlag, Sub(writeFlag.ref, Int(1)))),
                )
              ),
            )
          }

          else -> {
            blockingMutexes.forEach {
              actions.add(StmtLabel(AssumeStmt.of(Eq(it.lock.mutexFlag.ref, Int(0)))))
            }
            acquiredMutexes.forEach {
              val m = it.lock.mutexFlag
              actions.add(StmtLabel(AssignStmt.of(m, Add(m.ref, Int(1)))))
            }
            releasedMutexes.forEach {
              val m = it.lock.mutexFlag
              actions.add(StmtLabel(AssignStmt.of(m, Sub(m.ref, Int(1)))))
            }
          }
        }

        // Labels are atomic in XCFA semantics: no need to wrap them in an atomic block
        setOf(SequenceLabel(actions, metadata))
      }

      else -> setOf(this)
    }
  }

  private inline fun <reified T> descartes(sets: List<Set<T>>): Set<List<T>> =
    if (sets.isEmpty()) setOf()
    else
      sets
        .fold(setOf(listOf<T>())) { acc, set ->
          acc.flatMap { prefix -> set.map { element -> prefix + element } }.toSet()
        }
        .toSet()
}
