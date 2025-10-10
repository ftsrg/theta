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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Replaces mutexes (except the atomic block mutexes) with boolean variables. mutex_lock(mutex_var)
 * -> assume(!mutex_var); mutex_var := true; (atomically) mutex_unlock(mutex_var) -> mutex_var :=
 * false;
 */
class MutexToVarPass : ProcedurePass {

  private val mutexVars = mutableMapOf<String, VarDecl<BoolType>>()

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.parent.getVars().forEach { (v) ->
      if (v.type == BoolType.getInstance()) {
        mutexVars[v.name] = v as VarDecl<BoolType>
      }
    }

    builder.getEdges().toSet().forEach { edge ->
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(edge.label.replaceMutex()))
    }

    mutexVars.forEach { (_, v) -> builder.parent.addVar(XcfaGlobalVar(v, False())) }
    builder.parent.getInitProcedures().forEach { (proc, _) ->
      mutexVars.forEach { (_, v) ->
        val initEdge = proc.initLoc.outgoingEdges.first()
        val initLabels = initEdge.getFlatLabels()
        if (
          initLabels.none { it is StmtLabel && it.stmt is AssignStmt<*> && it.stmt.varDecl == v }
        ) {
          val assign = StmtLabel(AssignStmt.of(v, False()))
          val label = SequenceLabel(initLabels + assign, metadata = initEdge.label.metadata)
          proc.removeEdge(initEdge)
          proc.addEdge(initEdge.withLabel(label))
        }
      }
    }
    return builder
  }

  private fun XcfaLabel.replaceMutex(): XcfaLabel {
    return when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.replaceMutex() }, metadata)
      is FenceLabel -> {
        val actions = mutableListOf<XcfaLabel>()

        if (this is AtomicFenceLabel) {
          actions.add(this)
        } else {
          blockingMutexesWithoutAtomic.forEach {
            actions.add(StmtLabel(AssumeStmt.of(Not(it.name.mutexFlag.ref))))
          }
          acquiredMutexes.forEach {
            actions.add(StmtLabel(AssignStmt.of(it.name.mutexFlag, True())))
          }
          releasedMutexes.forEach {
            actions.add(StmtLabel(AssignStmt.of(it.name.mutexFlag, False())))
          }
        }

        // Labels are atomic in XCFA semantics: no need to wrap them in an atomic block
        SequenceLabel(actions, metadata)
      }

      else -> this
    }
  }

  private val String.mutexFlag
    get() = flag("_mutex_flag")

  private fun String.flag(prefix: String) =
    mutexVars.getOrPut(this) { Decls.Var("${prefix}_${ifEmpty { "atomic" }}", Bool()) }
}
