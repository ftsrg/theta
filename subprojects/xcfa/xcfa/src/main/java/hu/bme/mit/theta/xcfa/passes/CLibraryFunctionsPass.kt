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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import java.math.BigInteger

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
      "pthread_rwlock_rdlock",
      "pthread_rwlock_wrlock",
      "pthread_rwlock_unlock",
      "pthread_cond_wait",
      "pthread_cond_signal",
      "pthread_cond_broadcast",
      "pthread_mutex_init",
      "pthread_cond_init",
      "pthread_exit",
      "pthread_key_create",
      "pthread_getspecific",
      "pthread_setspecific",
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
                  val handle =
                    invokeLabel.params[1] // as? Dereference<*, *, *> ?: invokeLabel.getParam(1).ref
                  listOf(
                    JoinLabel(handle, metadata),
                    AssignStmtLabel(
                      invokeLabel.params[0] as RefExpr<*>,
                      getNullForType(invokeLabel.params[0].type),
                      metadata,
                    ),
                  )
                }

                "pthread_create" -> {
                  val handle =
                    Exprs.Dereference(
                      invokeLabel.params[1],
                      getNullForType(invokeLabel.params[1].type),
                      invokeLabel.params[1].type,
                    ) // as? Dereference<*, *, *> ?: invokeLabel.getParam(1).ref
                  val funcptr = invokeLabel.getParam(3)
                  val param = invokeLabel.params[4]
                  // int(0) to solve StartLabel not handling return params
                  listOf(
                    StartLabel(funcptr.name, listOf(Int(0), param), handle, metadata),
                    AssignStmtLabel(
                      invokeLabel.params[0] as RefExpr<*>,
                      getNullForType(invokeLabel.params[0].type),
                      metadata,
                    ),
                  )
                }

                "pthread_mutex_lock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(MutexLockLabel(handle, metadata))
                }

                "pthread_mutex_unlock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(MutexUnlockLabel(handle, metadata))
                }

                "pthread_mutex_trylock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  val ret = invokeLabel.getParam(0)
                  listOf(MutexTryLockLabel(handle, ret, metadata))
                }

                "pthread_rwlock_rdlock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(RWLockReadLockLabel(handle, metadata))
                }

                "pthread_rwlock_wrlock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(RWLockWriteLockLabel(handle, metadata))
                }

                "pthread_rwlock_unlock" -> {
                  val handle = invokeLabel.getMutexHandle(builder)
                  listOf(RWLockUnlockLabel(handle, metadata))
                }

                "pthread_cond_wait" -> {
                  val handle = invokeLabel.getMutexHandle(builder, 2)
                  // Due to spurious wakeup, it is basically equivalent to unlock+lock
                  listOf(MutexUnlockLabel(handle, metadata), MutexLockLabel(handle, metadata))
                }

                "pthread_cond_broadcast", // No need for special handling due to spurious wakeup
                "pthread_cond_signal", // No need for special handling due to spurious wakeup
                "pthread_mutex_init",
                "pthread_cond_init" -> listOf(NopLabel)

                "pthread_exit" -> {
                  target = builder.finalLoc.get()

                  builder.parent.getProcedures().forEach { proc ->
                    proc.getEdges().forEach { e ->
                      if (
                        e.getFlatLabels().any { l -> l is InvokeLabel && l.name == builder.name }
                      ) {
                        error("pthread_exit is not supported in invoked procedures")
                      }
                    }
                  }

                  listOf(NopLabel)
                }

                "pthread_key_create",
                "pthread_getspecific",
                "pthread_setspecific" -> {
                  invokeLabel.isLibraryFunction = true
                  listOf(invokeLabel)
                }

                else -> error("Unsupported library function ${invokeLabel.name}")
              }
            XcfaEdge(it.source, target, SequenceLabel(labels), metadata)
              .splitIf { label -> label is MutexUnlockLabel || label is MutexLockLabel }
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

  private fun <T : Type> getNullForType(t: T): Expr<T> =
    when (t) {
      is IntType -> Int(0) as Expr<T>
      is BvType -> BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, t.size) as Expr<T>
      else -> error("Unsupported type: $t")
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
