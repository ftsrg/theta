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
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.SubObjects
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.getAtomicBlockInnerLocations
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.integerOf
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
class CLibraryFunctionsPass(
  val parseContext: ParseContext,
  /** Model `strlen` exactly; off where the loop's unbounded memory could look like divergence. */
  private val modelStringLength: Boolean = false,
) : ProcedurePass {

  /** The procedures that the program defines; a call to one of them is not a library call. */
  private var defined: Set<String> = emptySet()

  /** The model that [bufferStubCalled] was computed for. */
  private var scanned: XcfaBuilder? = null

  /**
   * A stub writes a buffer somewhere but leaves cells stale that C writes, e.g., a terminated
   * string. An exact `strlen` or `atoi` over those cells could then prove a wrong Safe.
   */
  private var bufferStubCalled = false

  /**
   * The C zero of the variable's own type. The pthread functions return `int`, which is the SMT
   * `Int` only under integer arithmetic -- under bitvector arithmetic it is a `Bv`, and a hardcoded
   * `Int(0)` is then a type error.
   */
  private fun zeroOf(expr: Expr<*>): Expr<*> = CComplexType.getType(expr, parseContext).nullValue

  private val supportedFunctions =
    setOf(
      "strcpy",
      "pthread_join",
      "pthread_detach",
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
      "pthread_mutexattr_init",
      "pthread_mutexattr_settype",
      "pthread_mutexattr_destroy",
      "pthread_cond_init",
      "pthread_exit",
      "pthread_key_create",
      "pthread_getspecific",
      "pthread_setspecific",
      "pthread_mutex_timedlock",
      "pthread_cond_timedwait",
      "pthread_spin_lock",
      "pthread_spin_unlock",
      "pthread_spin_trylock",
    ) + NO_EFFECT_FUNCTIONS

  companion object {
    private val DECIMAL_PARSERS = setOf("atoi", "atol", "atoll")

    /** The largest array that the `atoi` model unrolls. */
    private const val MAX_UNROLLED_CELLS = 64

    /**
     * Metadata flag (keyed by a variable's name, like `cName`) marking a global variable that
     * encodes a C synchronization object whose source type is non-scalar (e.g. `pthread_mutex_t`,
     * `pthread_cond_t`, `pthread_rwlock_t`). Witness `c_expression` constraints must not reference
     * such variables, as their integer encoding (e.g. `m == 0`) is not a valid C expression.
     */
    const val SYNC_VAR_METADATA_KEY = "synchronizationObject"

    /** `_Atomic` global holding each started thread's return value, indexed by its result id. */
    const val THREAD_RESULTS = "__theta_thread_results"
    const val THREAD_NEXT_RESULT_ID = "__theta_thread_next_result_id"
    /** Prefix of the variable that holds the result id of the thread last started on a handle. */
    const val THREAD_RESULT_ID_PREFIX = "__theta_thread_result_id_"

    private var uniqueCounter = 0

    /** glibc's `ETIMEDOUT`. */
    private const val ETIMEDOUT = 110

    /**
     * Initialization and attributes whose only effects are process sharing, which matters only
     * across `fork` (never modeled), and scheduling, which constrains no interleaving.
     */
    private val NO_EFFECT_FUNCTIONS =
      setOf(
        "pthread_spin_init",
        "pthread_spin_destroy",
        "pthread_mutexattr_setpshared",
        "pthread_mutexattr_setprotocol",
        "pthread_mutexattr_setprioceiling",
        "pthread_condattr_init",
        "pthread_condattr_destroy",
        "pthread_condattr_setpshared",
        "pthread_condattr_setclock",
        "pthread_rwlockattr_init",
        "pthread_rwlockattr_destroy",
        "pthread_rwlockattr_setpshared",
        "pthread_rwlockattr_setkind_np",
      )
  }

  /** Tags [handle] as a synchronization object (no-op when no [parseContext] is available). */
  private fun markSynchronizationObject(handle: VarDecl<*>) {
    parseContext.metadata?.create(handle, SYNC_VAR_METADATA_KEY, true)
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
    defined = builder.parent.getProcedures().mapNotNull { it.name }.toSet()
    // Before the first LibraryStubsPass of the phase, so every such call is still an InvokeLabel.
    if (scanned !== builder.parent) {
      scanned = builder.parent
      bufferStubCalled =
        builder.parent.getProcedures().any { procedure ->
          procedure.getEdges().any { edge ->
            edge.getAllLabels().any {
              it is InvokeLabel &&
                it.name !in defined &&
                LibraryStubsPass.writesBufferInexactly(it, parseContext)
            }
          }
        }
    }
    val atomicLocations = getAtomicBlockInnerLocations(builder).toSet()
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      val atomicBefore =
        edges.runningFold(edge.source in atomicLocations) { atomic, part ->
          part.getFlatLabels().fold(atomic) { a, l ->
            when (l) {
              is AtomicBeginLabel -> true
              is AtomicEndLabel -> false
              else -> a
            }
          }
        }
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEachIndexed { index, it ->
          if (predicate((it.label as SequenceLabel).labels[0])) {
            val invokeLabel = it.label.labels[0] as InvokeLabel
            val metadata = invokeLabel.metadata
            var target = it.target

            val addSingle = { label: XcfaLabel ->
              builder.addEdge(XcfaEdge(it.source, target, SequenceLabel(listOf(label)), metadata))
            }
            // Instrumentation that has to be atomic, unless the call already is.
            val atomically = { labels: List<XcfaLabel> ->
              if (atomicBefore[index]) labels
              else listOf(AtomicBeginLabel(metadata)) + labels + AtomicEndLabel(metadata)
            }
            val addSeqFrom = { source: XcfaLocation, labels: List<XcfaLabel> ->
              XcfaEdge(source, target, SequenceLabel(labels), metadata)
                .splitIf { label -> label is MutexUnlockLabel || label is MutexLockLabel }
                .forEach(builder::addEdge)
            }
            val addSeq = { labels: List<XcfaLabel> -> addSeqFrom(it.source, labels) }
            val assignRet = { value: Int ->
              val ret = invokeLabel.params[0]
              AssignStmtLabel(
                ret as RefExpr<*>,
                CComplexType.getType(ret, parseContext).getValue("$value"),
                metadata,
              )
            }

            // list of edges, where an edge consists of a list of labels (for a SequenceLabel)
            when (invokeLabel.name) {
              "strcpy" -> {
                check(invokeLabel.params.size == 3) { "Two parameters expected for strcpy" }
                val copySource = invokeLabel.params[2]
                val copyTarget = invokeLabel.params[1]

                val type = copySource.type
                val indexVar = Decls.Var("__theta_strcpy_index_var_${uniqueCounter++}", type)
                builder.addVar(indexVar)
                val initLabel = AssignStmtLabel(indexVar, type.integerOf(0))
                val loc = XcfaLocation("${it.source.name}_strcpy", metadata = it.source.metadata)
                val initEdge = XcfaEdge(it.source, loc, SequenceLabel(listOf(initLabel)), metadata)
                builder.addEdge(initEdge)

                // the cells are `char`s: with the pointer type, bitvector cells were read in a
                // partition of their own, never written by the string's initialisation
                val sourceDeref = Dereference.of(copySource, indexVar.ref, charType(copySource))
                val targetDeref = Dereference.of(copyTarget, indexVar.ref, charType(copyTarget))

                val continueAssume =
                  StmtLabel(
                    AssumeStmt.of(NeqExpr.create2(sourceDeref, sourceDeref.type.integerOf(0)))
                  )
                val copyCurrent = StmtLabel(MemoryAssignStmt.of(targetDeref, sourceDeref))
                val increment =
                  AssignStmtLabel(indexVar.ref, Add(listOf(indexVar.ref, type.integerOf(1))))
                val copyLabel = SequenceLabel(listOf(continueAssume, copyCurrent, increment))
                val copyEdge = XcfaEdge(loc, loc, copyLabel, metadata)
                builder.addEdge(copyEdge)

                val exitAssume =
                  StmtLabel(
                    AssumeStmt.of(EqExpr.create2(sourceDeref, sourceDeref.type.integerOf(0)))
                  )
                // copy the terminating null byte as well
                val exitLabel = SequenceLabel(listOf(exitAssume, copyCurrent))
                val exitEdge = XcfaEdge(loc, target, exitLabel, metadata)
                builder.addEdge(exitEdge)
              }

              in DECIMAL_PARSERS ->
                addDecimalParse(invokeLabel, it.source, target, metadata, builder)

              "strlen" -> {
                // The index of the first 0 cell. The index has no C type, so it gets no overflow
                // check, and the cell reads get the usual memory-safety checks.
                val str = invokeLabel.params[1]
                val ret = invokeLabel.params[0] as RefExpr<*>
                val index = Decls.Var("__theta_strlen_index_var_${uniqueCounter++}", str.type)
                builder.addVar(index)
                val loc =
                  XcfaLocation(
                    "${it.source.name}_strlen_${uniqueCounter++}",
                    metadata = it.source.metadata,
                  )
                val init = AssignStmtLabel(index, str.type.integerOf(0))
                builder.addEdge(XcfaEdge(it.source, loc, SequenceLabel(listOf(init)), metadata))
                val cell = Dereference.of(str, index.ref, charType(str))
                val next =
                  listOf(
                    StmtLabel(AssumeStmt.of(NeqExpr.create2(cell, cell.type.integerOf(0)))),
                    AssignStmtLabel(index.ref, Add(listOf(index.ref, str.type.integerOf(1)))),
                  )
                builder.addEdge(XcfaEdge(loc, loc, SequenceLabel(next), metadata))
                val exit =
                  listOf(
                    StmtLabel(AssumeStmt.of(EqExpr.create2(cell, cell.type.integerOf(0)))),
                    AssignStmtLabel(ret, cast(index.ref, ret.type)),
                  )
                builder.addEdge(XcfaEdge(loc, target, SequenceLabel(exit), metadata))
              }

              "pthread_join" -> {
                val handle = invokeLabel.getParam(1)
                val retval = invokeLabel.params.getOrNull(2)?.takeUnless { it.isNullPointer() }
                // The joined thread is finished, so its slot is final: a plain read suffices.
                val storeResult =
                  retval?.let {
                    val results = threadResults(builder, it.type)
                    val id = resultIdVar(builder, invokeLabel.params[1], handle)
                    val offset = CComplexType.getSignedLong(parseContext).nullValue
                    StmtLabel(
                      MemoryAssignStmt.of(
                        Dereference.of(it, offset, it.type),
                        cast(
                          Read(
                            cast(results.ref, results.type as ArrayType<Type, Type>),
                            cast(id.ref, resultIdType),
                          ),
                          it.type,
                        ),
                      ),
                      metadata = metadata,
                    )
                  }
                addSeq(
                  listOfNotNull(
                    JoinLabel(handle, metadata),
                    storeResult,
                    AssignStmtLabel(
                      invokeLabel.params[0] as RefExpr<*>,
                      zeroOf(invokeLabel.params[0]),
                      metadata,
                    ),
                  )
                )
              }

              "pthread_create" -> {
                val handle = invokeLabel.getParam(1)
                val funcptr = invokeLabel.getParam(3)
                val startRoutine =
                  checkNotNull(builder.parent.getProcedures().find { it.name == funcptr.name }) {
                    "Unsupported pthread_create start routine `${funcptr.name}`: no such procedure exists. " +
                      "Only direct function symbols are supported as thread entry points."
                  }
                // the argument keeps its own C type (e.g. an int-typed NULL), whose width can
                // differ from the routine's `void *` parameter under LP64
                val param =
                  startRoutine.getParams().getOrNull(1)?.first?.let {
                    CComplexType.getType(it.ref, parseContext).castTo(invokeLabel.params[4])
                  } ?: invokeLabel.params[4]
                // A thread whose result may be joined gets a fresh result id as an extra argument;
                // ThreadResultPass makes its start routine store the result under it.
                val resultId =
                  if (threadResultsUsed(builder)) {
                    val id = resultIdVar(builder, invokeLabel.params[1], handle)
                    val next = nextResultId(builder)
                    // Passed through a local: start labels must not read atomic globals.
                    val arg =
                      Decls.Var("${THREAD_RESULT_ID_PREFIX}arg_${uniqueCounter++}", resultIdType)
                        .also(builder::addVar)
                    atomically(
                      listOf(
                        AssignStmtLabel(arg, next.ref, metadata),
                        AssignStmtLabel(id, next.ref, metadata),
                        AssignStmtLabel(
                          next,
                          Add(listOf(next.ref, next.type.integerOf(1))),
                          metadata,
                        ),
                      )
                    ) to arg
                  } else null
                // int(0) to solve StartLabel not handling return params
                addSeq(
                  (resultId?.first ?: emptyList()) +
                    listOf(
                      StartLabel(
                        funcptr.name,
                        listOfNotNull(Int(0), param, resultId?.second?.ref),
                        handle,
                        metadata,
                      ),
                      AssignStmtLabel(
                        invokeLabel.params[0] as RefExpr<*>,
                        zeroOf(invokeLabel.params[0]),
                        metadata,
                      ),
                    )
                )
              }

              "pthread_mutex_lock" -> {
                val handle = invokeLabel.getMutexHandle()
                addSingle(MutexLockLabel(handle, metadata))
              }

              "pthread_mutex_unlock" -> {
                val handle = invokeLabel.getMutexHandle()
                addSingle(MutexUnlockLabel(handle, metadata))
              }

              "pthread_mutex_trylock" -> {
                val handle = invokeLabel.getMutexHandle()
                val ret = invokeLabel.getParam(0)
                addSingle(MutexTryLockLabel(handle, ret, metadata))
              }

              // Timing out is possible exactly when the mutex is held, as a failing trylock is.
              "pthread_mutex_timedlock" -> {
                val handle = invokeLabel.getMutexHandle()
                val choice = choiceVar(builder)
                val choose =
                  XcfaLocation(
                    "${it.source.name}_timedlock${uniqueCounter++}",
                    metadata = it.source.metadata,
                  )
                builder.addEdge(
                  XcfaEdge(
                    it.source,
                    choose,
                    SequenceLabel(listOf(StmtLabel(Havoc(choice)))),
                    metadata,
                  )
                )
                addSeqFrom(
                  choose,
                  listOf(
                    StmtLabel(Assume(choice.ref)),
                    MutexLockLabel(handle, metadata),
                    assignRet(0),
                  ),
                )
                val tryLock = MutexTryLockLabel(handle, invokeLabel.getParam(0), metadata)
                addSeqFrom(choose, listOf(StmtLabel(Assume(Not(choice.ref))), tryLock))
              }

              "pthread_cond_timedwait" -> {
                invokeLabel.markSyncParam(1)
                val handle = invokeLabel.getMutexHandle(2)
                val choice = choiceVar(builder)
                val ret = invokeLabel.params[0]
                val retType = CComplexType.getType(ret, parseContext)
                val timedOut =
                  Ite<Type>(choice.ref, retType.getValue("$ETIMEDOUT"), retType.nullValue)
                addSeq(
                  listOf(
                    MutexUnlockLabel(handle, metadata),
                    MutexLockLabel(handle, metadata),
                    StmtLabel(Havoc(choice)),
                    AssignStmtLabel(ret as RefExpr<*>, timedOut, metadata),
                  )
                )
              }

              // A spin lock is a mutex that busy-waits, which no interleaving tells apart.
              "pthread_spin_lock" -> {
                addSeq(listOf(MutexLockLabel(invokeLabel.getMutexHandle(), metadata), assignRet(0)))
              }

              "pthread_spin_unlock" -> {
                addSeq(
                  listOf(MutexUnlockLabel(invokeLabel.getMutexHandle(), metadata), assignRet(0))
                )
              }

              "pthread_spin_trylock" -> {
                val ret = invokeLabel.getParam(0)
                addSingle(MutexTryLockLabel(invokeLabel.getMutexHandle(), ret, metadata))
              }

              in NO_EFFECT_FUNCTIONS -> {
                invokeLabel.markSyncParam(1)
                addSingle(assignRet(0))
              }

              "pthread_rwlock_rdlock" -> {
                val handle = invokeLabel.getMutexHandle()
                addSingle(RWLockReadLockLabel(handle, metadata))
              }

              "pthread_rwlock_wrlock" -> {
                val handle = invokeLabel.getMutexHandle()
                addSingle(RWLockWriteLockLabel(handle, metadata))
              }

              "pthread_rwlock_unlock" -> {
                val handle = invokeLabel.getMutexHandle()
                addSingle(RWLockUnlockLabel(handle, metadata))
              }

              "pthread_cond_wait" -> {
                invokeLabel.markSyncParam(1) // the condition variable (non-scalar source type)
                val handle = invokeLabel.getMutexHandle(2)
                // Due to spurious wakeup, it is basically equivalent to unlock+lock
                addSeq(listOf(MutexUnlockLabel(handle, metadata), MutexLockLabel(handle, metadata)))
              }

              "pthread_mutex_init",
              "pthread_mutexattr_init",
              "pthread_mutexattr_settype",
              "pthread_mutexattr_destroy" -> {
                invokeLabel.markSyncParam(1)
                if (invokeLabel.name == "pthread_mutex_init") invokeLabel.markSyncParam(2)
                invokeLabel.isLibraryFunction = true
                addSeq(
                  listOf(
                    invokeLabel,
                    AssignStmtLabel(
                      invokeLabel.params[0] as RefExpr<*>,
                      zeroOf(invokeLabel.params[0]),
                      metadata,
                    ),
                  )
                )
              }

              // Detaching only makes a thread unjoinable; it neither starts nor stops it, so it
              // has no effect on what may race. Left unmodelled it survived as a call to a
              // procedure that does not exist and brought down the race analysis' own procedure
              // classifier ("Unknown procedure: pthread_detach", DataRaceUtils#
              // getMultipleThreadsPerProcedure) -- which is reached only on the
              // datarace-to-reachability path, so it never showed up in ordinary runs.
              "pthread_detach",
              "pthread_cond_broadcast", // No need for special handling due to spurious wakeup
              "pthread_cond_signal", // No need for special handling due to spurious wakeup
              "pthread_cond_init" -> {
                // the mutex/condition object (non-scalar source type)
                invokeLabel.markSyncParam(1)
                addSingle(NopLabel)
              }

              "pthread_exit" -> {
                target = builder.finalLoc.get()

                builder.parent.getProcedures().forEach { proc ->
                  proc.getEdges().forEach { e ->
                    if (e.getFlatLabels().any { l -> l is InvokeLabel && l.name == builder.name }) {
                      error("pthread_exit is not supported in invoked procedures")
                    }
                  }
                }

                // The exit value is the thread's result, exactly as if the routine returned it. A
                // routine whose return slot cannot hold it is refused by ThreadResultPass.
                val ret = builder.getParams().firstOrNull { it.second == ParamDirection.OUT }?.first
                val value = invokeLabel.params.getOrNull(1)
                if (
                  ret != null &&
                    value != null &&
                    ret.type == value.type &&
                    threadResultsUsed(builder)
                ) {
                  addSingle(exitOf(builder, AssignStmtLabel(ret, value, metadata), metadata))
                } else addSingle(exitOf(builder, NopLabel, metadata))
              }

              "pthread_key_create",
              "pthread_getspecific",
              "pthread_setspecific" -> {
                addSeq(atomically(modelThreadSpecificCall(builder, invokeLabel, parseContext)))
              }

              else -> error("Unsupported library function ${invokeLabel.name}")
            }
          } else {
            builder.addEdge(it.withLabel(SequenceLabel(it.label.labels)))
          }
        }
      }
    }
    return builder
  }

  /** The SMT type of the `char`s that [ptr] (a `char *` or `char[]`) points to. */
  private fun charType(ptr: Expr<*>): Type =
    when (val t = CComplexType.getType(ptr, parseContext)) {
      is CPointer -> t.embeddedType.smtType
      is CArray -> t.embeddedType.smtType
      else -> error("strcpy on a non-pointer argument of type $t: $ptr")
    }

  private fun choiceVar(builder: XcfaProcedureBuilder): VarDecl<BoolType> =
    Decls.Var("__theta_pthread_choice_${uniqueCounter++}", Bool()).also(builder::addVar)

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

  private fun predicate(it: XcfaLabel): Boolean =
    it is InvokeLabel &&
      (it.name in supportedFunctions ||
        (it.name == "strlen" && modelsStringLength(it)) ||
        (it.name in DECIMAL_PARSERS && modelsDecimalParse(it)))

  /** `atoi` and friends on a plain variable, under the same conditions as `strlen`. */
  private fun modelsDecimalParse(invoke: InvokeLabel): Boolean {
    if (!modelStringLength || bufferStubCalled) return false
    if (invoke.name in defined || invoke.params.size != 2) return false
    if (invoke.params[0] !is RefExpr<*>) return false
    val str = invoke.params[1] as? RefExpr<*> ?: return false
    val type = CComplexType.getType(str, parseContext)
    return type is CPointer || type is CArray
  }

  /**
   * `atoi`, `atol` and `atoll` as glibc computes them: `strtol(s, NULL, 10)` (`strtoll` for
   * `atoll`), converted to the return type modulo 2^w. Skip white space, read a sign and the
   * decimal digits, and saturate at the limits of the parsed type. The state has no C type, so it
   * gets no overflow check.
   *
   * Each character is one block of assignments. Over an array of at most [MAX_UNROLLED_CELLS]
   * cells, the blocks of all cells are one edge, so that the program stays acyclic and BMC takes
   * one step. If no cell ends the number, C reads the cell after the array: the model reads it
   * (memory safety checks it) and ends the path. Otherwise one loop edge per character.
   */
  private fun addDecimalParse(
    invoke: InvokeLabel,
    source: XcfaLocation,
    target: XcfaLocation,
    metadata: MetaData,
    builder: XcfaProcedureBuilder,
  ) {
    val str = invoke.params[1]
    val ret = invoke.params[0] as RefExpr<*>
    val parsed =
      if (invoke.name == "atoll") CComplexType.getSignedLongLong(parseContext)
      else CComplexType.getSignedLong(parseContext)
    val max = BigInteger.TWO.pow(parsed.width() - 1).dec()
    val min = max.inc().negate()
    val limit = max / BigInteger.TEN
    val num = { v: BigInteger -> parsed.smtType.integerOf(v)!! }
    val size =
      (CComplexType.getType(str, parseContext) as? CArray)
        ?.let { SubObjects(parseContext).fixedArraySize(it) }
        ?.takeIf { it in 1..MAX_UNROLLED_CELLS }
    // The digits of a terminated string in the array cannot reach the limit: saturation together
    // with the conversion modulo 2^w makes the query far harder, so it is left out then.
    val saturates = size == null || BigInteger.TEN.pow(size - 1).dec() > max
    val id = uniqueCounter++
    val name = "__theta_${invoke.name}_$id"
    val char = charType(str)
    val acc = Decls.Var("${name}_acc", parsed.smtType)
    val digit = Decls.Var("${name}_digit", parsed.smtType)
    val ch = Decls.Var("${name}_char", char)
    val flag = { kind: String -> Decls.Var("${name}_$kind", Bool()) }
    val neg = flag("neg")
    val sat = flag("sat")
    val started = flag("started")
    val done = flag("done")
    val lead = flag("lead")
    val isDigit = flag("isdigit")
    val stop = flag("stop")
    (listOf(acc, digit, ch) + listOf(neg, sat, started, done, lead, isDigit, stop)).forEach(
      builder::addVar
    )
    val index =
      if (size == null) Decls.Var("${name}_index", str.type).also(builder::addVar) else null
    val cell = { i: Int -> Dereference.of(str, index?.ref ?: str.type.integerOf(i), char) }
    val isChar = { values: List<Int> ->
      Or(values.map { Eq(ch.ref, char.integerOf(it)) as Expr<BoolType> })
    }
    val space = isChar(listOf(32, 9, 10, 11, 12, 13))
    val sign = isChar(listOf('-'.code, '+'.code))
    val isDigitChar =
      And(Geq(ch.ref, char.integerOf('0'.code)), Leq(ch.ref, char.integerOf('9'.code)))
    // linear in the character, which the solver handles far better than an ite over the digits
    val charCType =
      when (val t = CComplexType.getType(str, parseContext)) {
        is CPointer -> t.embeddedType
        is CArray -> t.embeddedType
        else -> error("atoi on a non-pointer argument of type $t: $str")
      }
    parseContext.metadata.create(ch.ref, "cType", charCType)
    val value = Sub(parsed.castTo(ch.ref), num(BigInteger.valueOf('0'.code.toLong())))
    val upper = num(limit)
    val lower = num(limit.negate())
    val overflow =
      Or(
        And(
          neg.ref,
          Or(
            Lt(acc.ref, lower) as Expr<BoolType>,
            And(Eq(acc.ref, lower), Gt(digit.ref, num(min.negate().mod(BigInteger.TEN)))),
          ),
        ),
        And(
          Not(neg.ref),
          Or(
            Gt(acc.ref, upper) as Expr<BoolType>,
            And(Eq(acc.ref, upper), Gt(digit.ref, num(max.mod(BigInteger.TEN)))),
          ),
        ),
      )
    val shifted = Mul(acc.ref, num(BigInteger.TEN))
    val next = Ite<Type>(neg.ref, Sub(shifted, digit.ref), Add(shifted, digit.ref))
    // the conditions read the state before the character, so they are computed first
    val block = { read: Expr<*> ->
      listOf(
        AssignStmtLabel(ch, read),
        AssignStmtLabel(lead, And(Not(started.ref), Not(done.ref))),
        AssignStmtLabel(
          isDigit,
          And(Not(done.ref), Or(started.ref, Not(Or(space, sign))), isDigitChar),
        ),
        AssignStmtLabel(
          stop,
          And(Not(done.ref), Or(started.ref, Not(Or(space, sign))), Not(isDigitChar)),
        ),
        AssignStmtLabel(neg, Or(neg.ref, And(lead.ref, isChar(listOf('-'.code))))),
        AssignStmtLabel(digit, value),
        AssignStmtLabel(
          sat,
          if (saturates) Or(sat.ref, And(isDigit.ref, overflow)) else Bool(false),
        ),
        AssignStmtLabel(acc, Ite<Type>(And(isDigit.ref, Not(sat.ref)), next, acc.ref)),
        AssignStmtLabel(done, Or(done.ref, stop.ref)),
        AssignStmtLabel(started, Or(started.ref, And(lead.ref, Not(space)))),
      )
    }
    val init =
      listOfNotNull(index?.let { AssignStmtLabel(it, str.type.integerOf(0)) }) +
        AssignStmtLabel(acc, num(BigInteger.ZERO)) +
        listOf(neg, sat, started, done).map { AssignStmtLabel(it, Bool(false)) }
    val loc = { kind: String ->
      XcfaLocation("${source.name}_${invoke.name}_${id}_$kind", metadata = source.metadata)
    }
    val edge = { from: XcfaLocation, to: XcfaLocation, labels: List<XcfaLabel> ->
      builder.addEdge(XcfaEdge(from, to, SequenceLabel(labels), metadata))
    }
    val assume = { cond: Expr<BoolType> -> StmtLabel(Assume(cond)) }
    val parsedLoc = loc("parsed")
    if (size != null) {
      edge(source, parsedLoc, init + (0 until size).flatMap { block(cell(it)) })
      val past = Decls.Var("${name}_past", char).also(builder::addVar)
      edge(parsedLoc, loc("past"), listOf(assume(Not(done.ref)), AssignStmtLabel(past, cell(size))))
    } else {
      val loop = loc("loop")
      edge(source, loop, init)
      val step = AssignStmtLabel(index!!.ref, Add(listOf(index.ref, str.type.integerOf(1))))
      edge(loop, loop, listOf(assume(Not(done.ref))) + block(cell(0)) + step)
      edge(loop, parsedLoc, listOf(assume(done.ref)))
    }
    val result = Ite<Type>(sat.ref, Ite<Type>(neg.ref, num(min), num(max)), acc.ref)
    edge(
      parsedLoc,
      target,
      listOf(assume(done.ref), AssignStmtLabel(ret, cast(convert(result, parsed, ret), ret.type))),
    )
  }

  /** [value] of the C type [from] converted to the type of [ret] modulo 2^w, as gcc does. */
  private fun convert(value: Expr<*>, from: CComplexType, ret: Expr<*>): Expr<*> {
    val retType = CComplexType.getType(ret, parseContext)
    // the integer encoding keeps a narrowing signed conversion unwrapped, so wrap explicitly
    return if (value.type is IntType && retType.width() < from.width()) {
      val half = BigInteger.TWO.pow(retType.width() - 1)
      Sub(Mod(Add(value, Int(half)), Int(half.shiftLeft(1))), Int(half))
    } else {
      parseContext.metadata.create(value, "cType", from)
      retType.castTo(value)
    }
  }

  /**
   * `strlen` on a plain variable, when the program does not define it and no stub writes a buffer.
   * A pointer sum would name no object under the multi model (`Dereference(p + k, i)`), so such a
   * call stays a stub.
   */
  private fun modelsStringLength(invoke: InvokeLabel): Boolean {
    if (!modelStringLength || bufferStubCalled) return false
    if (invoke.name in defined || invoke.params.size != 2) return false
    val ret = invoke.params[0] as? RefExpr<*> ?: return false
    val str = invoke.params[1] as? RefExpr<*> ?: return false
    if (ret.type != str.type) return false
    val type = CComplexType.getType(str, parseContext)
    return type is CPointer || type is CArray
  }

  private fun Expr<*>.isNullPointer() = asConstant()?.signum() == 0

  /**
   * Whether some `pthread_join` may store a thread's result: one not lowered yet, or one already
   * lowered, which has created [THREAD_RESULTS]. Only then are thread starts instrumented.
   */
  /** A `pthread_exit` label, which in the initial thread also marks where its locals die. */
  private fun exitOf(
    builder: XcfaProcedureBuilder,
    exit: XcfaLabel,
    metadata: MetaData,
  ): XcfaLabel =
    if (
      parseContext.isCheckMemsafety &&
        builder.parent.getInitProcedures().any { it.first == builder }
    )
      SequenceLabel(listOf(exit, InvokeLabel(MAIN_THREAD_EXIT, listOf(), metadata)), metadata)
    else exit

  private fun threadResultsUsed(builder: XcfaProcedureBuilder): Boolean =
    builder.parent.getVars().any { it.wrappedVar.name == THREAD_RESULTS } ||
      builder.parent.getProcedures().any { proc ->
        proc.getEdges().any { e ->
          e.getFlatLabels().any {
            it is InvokeLabel &&
              it.name == "pthread_join" &&
              it.params.getOrNull(2)?.isNullPointer() == false
          }
        }
      }

  private val resultIdType
    get() = CComplexType.getSignedInt(parseContext).smtType

  private fun atomicGlobal(builder: XcfaProcedureBuilder, name: String, type: Type): VarDecl<*> =
    builder.parent.getVars().firstOrNull { it.wrappedVar.name == name }?.wrappedVar
      ?: Decls.Var(name, type).also {
        builder.parent.addVar(XcfaGlobalVar(it, type.defaultValue, atomic = true))
      }

  private fun threadResults(builder: XcfaProcedureBuilder, resultType: Type): VarDecl<*> =
    atomicGlobal(builder, THREAD_RESULTS, ArrayType.of(resultIdType, resultType)).also {
      check((it.type as ArrayType<*, *>).elemType == resultType) {
        "Unsupported pthread_join: retval of type $resultType"
      }
    }

  private fun nextResultId(builder: XcfaProcedureBuilder): VarDecl<*> =
    atomicGlobal(builder, THREAD_NEXT_RESULT_ID, resultIdType)

  /**
   * The variable holding the result id of the thread last started on [handle], in the scope of the
   * handle's own variable ([param] is the handle argument as written, e.g. `&t[1]`), so that the
   * create and the join of one handle agree on it.
   */
  private fun resultIdVar(
    builder: XcfaProcedureBuilder,
    param: Expr<*>,
    handle: VarDecl<*>,
  ): VarDecl<*> {
    var base: Expr<*> = param
    while (true) {
      base =
        when (base) {
          is Reference<*, *> -> base.expr
          is Dereference<*, *, *> -> base.array
          is PosExpr<*> -> base.op
          is AddExpr<*> -> base.ops.single { it.asConstant() == null }
          else -> break
        }
    }
    val decl = (base as? RefExpr<*>)?.decl
    val name = "$THREAD_RESULT_ID_PREFIX${handle.name}"
    return when {
      decl in builder.getVars() ->
        builder.getVars().firstOrNull { it.name == name }
          ?: Decls.Var(name, resultIdType).also(builder::addVar)
      builder.parent.getVars().any { it.wrappedVar == decl } ->
        atomicGlobal(builder, name, resultIdType)
      else -> error("Unsupported pthread handle for a thread result: $param")
    }
  }

  private fun Expr<*>.asConstant(): BigInteger? =
    when (this) {
      is IntLitExpr -> value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this)
      // A constant that has not been folded yet is still a constant. Unrolling substitutes the
      // index but leaves the unsigned-wraparound wrapper the frontend put around it, so the offset
      // of `&t[4]` arrives as `(mod 4 4294967296)` -- matching only a bare literal rejected the
      // handle as "non-constant dereference offset" even though its value is perfectly known.
      else ->
        ExprUtils.simplify(this).let { simplified ->
          when (simplified) {
            is IntLitExpr -> simplified.value
            is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(simplified)
            else -> null
          }
        }
    }

  /**
   * A distinct thread/mutex handle per array element `t[i]`. A pthread handle is an identity key (a
   * [VarDecl] the analysis maps to a thread id, matching a start to its join); an array of handles
   * -- `pthread_t t[3]` with `pthread_create(&t[i], …)` / `pthread_join(t[i], …)` -- needs a
   * distinct one per element, and `&t[i]` and `t[i]` for the same constant `i` must resolve to the
   * *same* key. The element index has to be a compile-time constant, which is why the create/join
   * loops are unrolled before this pass runs (see the extra [UnrollPass] in [CPasses]).
   */
  private val arrayElementHandles = mutableMapOf<Pair<VarDecl<*>, BigInteger>, VarDecl<*>>()

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
        val base = (param.array as RefExpr<*>).decl
        check(base is VarDecl<*>)
        val offset =
          checkNotNull(param.offset.asConstant()) {
            // A non-constant offset is a not-yet-unrolled loop handle (`&t[i]`); the create/join
            // loops are unrolled and their index folded (PthreadArrayHandleUnrollPass + the
            // SimplifyExprsPass after it) before this pass runs.
            "Unsupported library parameter: non-constant dereference offset (${param.offset})"
          }
        elementHandle(base, offset)
      }

      // `t + i`, the pointer-arithmetic spelling of `&t[i]`: one base variable plus constants.
      is AddExpr<*> -> {
        val ops = param.ops.map { it to it.asConstant() }
        var base = ops.filter { it.second == null }.map { it.first }.singleOrNull()
        while (base is PosExpr<*>) base = base.op
        check(base is RefExpr<*> && base.decl is VarDecl<*>) {
          "Unsupported library parameter: expected a reference base variable plus a constant " +
            "offset, got $param"
        }
        elementHandle(base.decl as VarDecl<*>, ops.sumOf { it.second ?: BigInteger.ZERO })
      }

      else -> error("Unsupported library parameter expression: $param")
    }
  }

  private fun elementHandle(base: VarDecl<*>, offset: BigInteger): VarDecl<*> =
    // Offset 0 keeps mapping to the base variable itself -- unchanged for the scalar and
    // single-object cases -- while every higher element gets its own synthetic handle.
    if (offset == BigInteger.ZERO) base
    else
      arrayElementHandles.getOrPut(base to offset) { Decls.Var("${base.name}_$offset", base.type) }

  private fun InvokeLabel.getMutexHandle(index: Int = 1): Expr<*> = params[index]
}
