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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import java.math.BigInteger

/**
 * Transforms the library procedure calls with names in supportedFunctions into model elements.
 * Requires the ProcedureBuilder be `deterministic`.
 *
 * When a [parseContext] is given, every variable that is used as a handle of a C synchronization
 * object (a `pthread_mutex_t`/`pthread_cond_t`/`pthread_rwlock_t`) is tagged with the
 * [SYNC_VAR_METADATA_KEY] metadata flag. Theta models such non-scalar objects as plain integers, so
 * their valuations (e.g. `m == 0`) are not legal C expressions over the original program; consumers
 * that emit C-expression constraints (e.g. violation witnesses) use this flag to exclude them.
 */
class CLibraryFunctionsPass(private val parseContext: ParseContext? = null) : ProcedurePass {

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

    /**
     * Metadata flag (keyed by a variable's name, like `cName`) marking a global variable that
     * encodes a C synchronization object whose source type is non-scalar (e.g. `pthread_mutex_t`,
     * `pthread_cond_t`, `pthread_rwlock_t`). Witness `c_expression` constraints must not reference
     * such variables, as their integer encoding (e.g. `m == 0`) is not a valid C expression.
     */
    const val SYNC_VAR_METADATA_KEY = "synchronizationObject"
  }

  /** Tags [handle] as a synchronization object (no-op when no [parseContext] is available). */
  private fun markSynchronizationObject(handle: VarDecl<*>) {
    parseContext?.metadata?.create(handle.name, SYNC_VAR_METADATA_KEY, true)
  }

  /** Best-effort tagging of the synchronization object referenced by parameter [index], if any. */
  private fun InvokeLabel.markSyncParam(index: Int) {
    if (index >= params.size) return
    var param = params[index]
    while (param is Reference<*, *>) param = param.expr
    ((param as? RefExpr<*>)?.decl as? VarDecl<*>)?.let(::markSynchronizationObject)
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
                      AssignStmtLabel(arg, expr)
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
                    AssignStmtLabel(invokeLabel.params[0] as RefExpr<*>, Int(0)),
                  )
                }

                "pthread_create" -> {
                  val handle = invokeLabel.getParam(1)
                  val funcptr = invokeLabel.getParam(3)
                  check(builder.parent.getProcedures().any { it.name == funcptr.name }) {
                    "Unsupported pthread_create start routine `${funcptr.name}`: no such procedure exists. " +
                      "Only direct function symbols are supported as thread entry points."
                  }
                  val param = invokeLabel.params[4]
                  // int(0) to solve StartLabel not handling return params
                  listOf(
                    StartLabel(funcptr.name, listOf(Int(0), param), handle, metadata),
                    AssignStmtLabel(invokeLabel.params[0] as RefExpr<*>, Int(0)),
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
                  invokeLabel.markSyncParam(1) // the condition variable (non-scalar source type)
                  val handle = invokeLabel.getMutexHandle(builder, 2)
                  // Due to spurious wakeup, it is basically equivalent to unlock+lock
                  listOf(MutexUnlockLabel(handle, metadata), MutexLockLabel(handle, metadata))
                }

                "pthread_cond_broadcast", // No need for special handling due to spurious wakeup
                "pthread_cond_signal", // No need for special handling due to spurious wakeup
                "pthread_mutex_init",
                "pthread_cond_init" -> {
                  invokeLabel.markSyncParam(
                    1
                  ) // the mutex/condition object (non-scalar source type)
                  listOf(NopLabel)
                }

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

  private fun predicate(it: XcfaLabel): Boolean = it is InvokeLabel && it.name in supportedFunctions

  private fun Expr<*>.isLiteralZero(): Boolean =
    when (this) {
      is IntLitExpr -> value == BigInteger.ZERO
      is BvLitExpr -> value.all { !it }
      else -> false
    }

  private fun InvokeLabel.getParam(index: Int): VarDecl<*> {
    var param = params[index]
    while (param is Reference<*, *>) param = param.expr
    return when (param) {
      is RefExpr<*> -> {
        check(param.decl is VarDecl<*>)
        param.decl as VarDecl<*>
      }

      is Dereference<*, *, *> -> {
        check(param.array is RefExpr<*>) {
          "Unsupported library parameter: expected reference base variable, got ${param.array}"
        }
        check(param.offset.isLiteralZero()) {
          "Unsupported library parameter: non-zero dereference offsets are not supported (${param.offset})"
        }
        val base = param.array as RefExpr<*>
        check(base.decl is VarDecl<*>)
        base.decl as VarDecl<*>
      }

      else -> error("Unsupported library parameter expression: $param")
    }
  }

  private fun InvokeLabel.getMutexHandle(
    builder: XcfaProcedureBuilder,
    index: Int = 1,
  ): VarDecl<*> {
    val handle = getParam(index)
    checkMutexDecl(handle, builder)
    markSynchronizationObject(handle)
    return handle
  }
}
