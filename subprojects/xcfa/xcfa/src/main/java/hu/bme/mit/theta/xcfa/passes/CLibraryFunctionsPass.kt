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

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * Transforms the library procedure calls with names in supportedFunctions into model elements.
 * Requires the ProcedureBuilder be `deterministic`.
 */
class CLibraryFunctionsPass : ProcedurePass {

  private val supportedFunctions =
    setOf(
      "printf",
      "scanf",
      "pthread_join",
      "pthread_create",
      "pthread_mutex_lock",
      "pthread_mutex_unlock",
      "pthread_mutex_trylock",
      "pthread_cond_wait",
      "pthread_cond_signal",
      "pthread_cond_broadcast",
      "pthread_mutex_init",
      "pthread_cond_init",
      "pthread_exit",
    )

  companion object {
    private var printfCounter = 0
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          if (predicate((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            val metadata = invokeLabel.metadata
            var target = it.target
            val labels: List<XcfaLabel> =
              when (invokeLabel.name) {
                "printf" -> {
                  val printfCounter = printfCounter++
                  (2 until invokeLabel.params.size)
                    .mapIndexed { index, param ->
                      val expr = invokeLabel.params[param]
                      val arg = Decls.Var("__printf_arg_${printfCounter}_$index", expr.type)
                      builder.addVar(arg)
                      AssignStmtLabel(arg, expr, metadata)
                    }
                    .run { ifEmpty { listOf(NopLabel) } }
                }

                "scanf" -> {
                  check(invokeLabel.params.size >= 3) {
                    "At least two parameters (format string and one variable) expected in scanf"
                  }
                  (2 until invokeLabel.params.size).map { index ->
                    val param = invokeLabel.getParam(index)
                    StmtLabel(HavocStmt.of(param), metadata = metadata)
                  }
                }

                "pthread_join" -> {
                  val handle = invokeLabel.getParam(1)
                  listOf(
                    JoinLabel(handle, metadata),
                    AssignStmtLabel(invokeLabel.params[0] as RefExpr<*>, Int(0), metadata),
                  )
                }

                "pthread_create" -> {
                  val handle = invokeLabel.getParam(1)
                  val funcptr = invokeLabel.getParam(3)
                  val param = invokeLabel.params[4]
                  // int(0) to solve StartLabel not handling return params
                  listOf(
                    StartLabel(funcptr.name, listOf(Int(0), param), handle, metadata),
                    AssignStmtLabel(invokeLabel.params[0] as RefExpr<*>, Int(0), metadata),
                  )
                }

                "pthread_mutex_lock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(FenceLabel(setOf("mutex_lock(${handle.name})"), metadata))
                }

                "pthread_mutex_unlock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(FenceLabel(setOf("mutex_unlock(${handle.name})"), metadata))
                }

                "pthread_mutex_trylock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(FenceLabel(setOf("mutex_trylock(${handle.name})"), metadata))
                }

                "pthread_cond_wait" -> {
                  val cond = invokeLabel.getParam(1)
                  val handle = invokeLabel.getMutexHandle(builder, 2)
                  listOf(
                    FenceLabel(setOf("start_cond_wait(${cond.name},${handle.name})"), metadata),
                    FenceLabel(setOf("cond_wait(${cond.name},${handle.name})"), metadata),
                  )
                }

                "pthread_cond_broadcast",
                "pthread_cond_signal" -> {
                  val cond = invokeLabel.getParam(1)
                  listOf(FenceLabel(setOf("cond_signal(${cond.name})"), metadata))
                }

                "pthread_mutex_init",
                "pthread_cond_init" -> listOf(NopLabel)

                "pthread_exit" -> {
                  target = builder.finalLoc.get()
                  listOf(FenceLabel(setOf("pthread_exit"), metadata))
                }

                else -> error("Unsupported library function ${invokeLabel.name}")
              }
            XcfaEdge(it.source, target, SequenceLabel(labels), metadata)
              .splitIf { label ->
                label is FenceLabel && label.labels.any { l -> l.startsWith("start_cond_wait") }
              }
              .forEach(builder::addEdge)
          } else {
            builder.addEdge(it.withLabel(SequenceLabel(it.label.labels)))
          }
        }
      }
    }
    return builder
  }

  private fun checkMutexDecl(mutex: Decl<*>, builder: XcfaProcedureBuilder) {
    check(mutex is VarDecl<*> && mutex in builder.parent.getVars().map { it.wrappedVar }) {
      "Local mutex handles are not supported: ${mutex.name}"
    }
    val writes =
      builder.parent.getProcedures().sumOf { proc ->
        proc.getEdges().count { edge ->
          edge.collectVarsWithAccessType().any { (v, access) -> v == mutex && access.isWritten }
        }
      }
    check(writes <= 1) {
      "Non-static mutex handles (multiple writes) are not supported: ${mutex.name}"
    }
  }

  private fun predicate(it: XcfaLabel): Boolean = it is InvokeLabel && it.name in supportedFunctions

  private fun InvokeLabel.getParam(index: Int): VarDecl<*> {
    var param = params[index]
    while (param is Reference<*, *>) param = param.expr
    check(param is RefExpr && param.decl is VarDecl<*>)
    return param.decl as VarDecl<*>
  }

  private fun InvokeLabel.getMutexHandle(
    builder: XcfaProcedureBuilder,
    index: Int = 1,
  ): VarDecl<*> {
    val handle = getParam(index)
    checkMutexDecl(handle, builder)
    return handle
  }
}
