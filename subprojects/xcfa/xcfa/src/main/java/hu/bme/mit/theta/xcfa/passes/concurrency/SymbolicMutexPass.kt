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
package hu.bme.mit.theta.xcfa.passes.concurrency

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.passes.splitIf
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.intValue
import hu.bme.mit.theta.xcfa.utils.integerOf
import java.util.Collections
import java.util.IdentityHashMap

private val mutexLibraryFunctions =
  setOf(
    "pthread_mutex_init",
    "pthread_mutexattr_init",
    "pthread_mutexattr_settype",
    "pthread_mutexattr_destroy",
  )

internal val XcfaLabel.mutexAddresses: List<Expr<*>>
  get() =
    when {
      this is AtomicFenceLabel -> emptyList()
      this is FenceLabel -> listOf(lock)
      this is InvokeLabel && isLibraryFunction && name in mutexLibraryFunctions ->
        if (name == "pthread_mutex_init") listOf(params[1], params[2]) else listOf(params[1])
      else -> emptyList()
    }

internal fun XcfaLabel.withMutexAddresses(addresses: List<Expr<*>>): XcfaLabel =
  when (this) {
    is FenceLabel -> withLock(addresses.single())
    is InvokeLabel ->
      this.withParamsIndexed { i, arg ->
        if (i == 0 || i > addresses.size) arg else addresses[i - 1]
      }
    else -> error("Not a mutex operation: $this")
  }

/** Lowers all ordinary mutex operations of an XCFA to atomic, guarded array updates. */
class SymbolicMutexPass : ProcedurePass {
  private val processed = Collections.newSetFromMap(IdentityHashMap<XcfaBuilder, Boolean>())
  private var temporary = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val model = builder.parent
    if (!processed.add(model)) return builder
    val labels = model.getProcedures().flatMap { it.getEdges() }.flatMap { it.getAllLabels() }
    if (labels.none { it.mutexAddresses.isNotEmpty() }) return builder

    val recursive =
      labels.filterIsInstance<InvokeLabel>().any {
        if (!it.isLibraryFunction || it.name != "pthread_mutexattr_settype") false
        else {
          val setting = (ExprUtils.simplify(it.params[2]) as? LitExpr<*>)?.intValue
          checkNotNull(setting) { "Unknown mutex type: ${it.params[2]}" }
          MutexType.fromConstant(setting) == MutexType.RECURSIVE
        }
      }
    val initializers = mutableListOf<XcfaLabel>()
    fun <T : Type> global(name: String, value: LitExpr<T>): VarDecl<T> =
      Var(name, value.type).also {
        model.addVar(XcfaGlobalVar(it, value, atomic = true))
        initializers.add(StmtLabel(Assign(it, value)))
      }

    val arrays =
      labels
        .flatMap { it.mutexAddresses }
        .map { it.type }
        .distinct()
        .mapIndexed { i, type ->
          val simple =
            labels.any {
              (it is MutexLockLabel || it is MutexUnlockLabel || it is MutexTryLockLabel) &&
                (it as FenceLabel).lock.type == type
            }
          val rw =
            labels.any {
              (it is RWLockReadLockLabel ||
                it is RWLockWriteLockLabel ||
                it is RWLockUnlockLabel) && (it as FenceLabel).lock.type == type
            }
          Arrays(
              if (simple) global("__theta_simple_mutexes_$i", constant(type, Int(-1))) else null,
              if (recursive) global("__theta_recursive_$i", constant(type, False())) else null,
              if (simple && recursive) global("__theta_acquisitions_$i", constant(type, Int(0)))
              else null,
              if (rw) global("__theta_rw_mutexes_$i", constant(type, constant(Int(), emptyOwners)))
              else null,
            )
            .let { type to it }
        }
        .toMap()

    var roots = model.getInitProcedures().toList()
    check(roots.isNotEmpty()) { "Symbolic mutex encoding requires an entry point." }
    // An entry point can also be called or started. Keep its root-only initialization out of
    // those executions by making a separate entry copy in that case.
    var entryCopy: XcfaProcedureBuilder? = null
    if (roots.size == 1) {
      val (root, args) = roots.single()
      if (
        labels.any {
          (it is InvokeLabel && !it.isLibraryFunction && it.name == root.name) ||
            (it is StartLabel && it.name == root.name)
        }
      ) {
        val entry =
          root.deepCopy("symbolic_mutex_entry").also {
            it.name = freshProcedureName(model, "${root.name}__theta_mutex_entry")
          }
        model.replaceEntryPoints(listOf(entry to args))
        entryCopy = entry
        roots = model.getInitProcedures().toList()
      }
    }
    val procedures = model.getProcedures().toList()
    val root = roots.singleOrNull()?.first
    val tids =
      procedures.withIndex().associate { (index, procedure) ->
        procedure to
          Var("__theta_mutex_tid_$index", Int()).also {
            if (procedure === root) procedure.addVar(it)
            else procedure.addParam(it, ParamDirection.IN)
          }
      }
    val byName = procedures.associateBy { it.name }
    val shared = model.getVars().filter { !it.atomic }.map { it.wrappedVar }.toSet()
    fun needsSnapshot(label: XcfaLabel) =
      label is FenceLabel &&
        label !is AtomicFenceLabel &&
        (label.lock.dereferences.isNotEmpty() || ExprUtils.getVars(label.lock).any { it in shared })
    val nextTid =
      if (labels.any { it is StartLabel }) global("__theta_next_thread_id", Int(roots.size))
      else null

    for (procedure in procedures) {
      val tid = tids.getValue(procedure).ref
      fun replace(label: XcfaLabel): List<List<XcfaLabel>> =
        when (label) {
          is SequenceLabel ->
            label.labels.fold(listOf(emptyList())) { acc, child ->
              acc.flatMap { prefix -> replace(child).map { prefix + it } }
            }
          is NondetLabel -> label.labels.flatMap { replace(it) }
          is AtomicFenceLabel -> listOf(listOf(label))
          is FenceLabel -> arrays.getValue(label.lock.type).fence(label, tid)
          is InvokeLabel ->
            when {
              label.isLibraryFunction && label.name in mutexLibraryFunctions ->
                library(label, arrays, recursive)
              !label.isLibraryFunction && label.name in byName ->
                listOf(
                  listOf(label.copy(paramDirs = label.paramDirs + listOf(tid to ParamDirection.IN)))
                )
              else -> listOf(listOf(label))
            }
          is StartLabel -> {
            val counter = checkNotNull(nextTid)
            val childTid = Var("__theta_child_tid_${temporary++}", Int())
            procedure.addVar(childTid)
            listOf(
              listOf(
                StmtLabel(Assign(childTid, counter.ref), metadata = label.metadata),
                StmtLabel(Assign(counter, Inc(counter.ref)), metadata = label.metadata),
                label.copy(params = label.params + childTid.ref),
              )
            )
          }
          else -> listOf(listOf(label))
        }
      // A handle is live only from its snapshot to the operation, so one per type suffices, and
      // clearing it there keeps it from distinguishing otherwise equal states.
      val handles = mutableMapOf<Type, VarDecl<*>>()
      for (edge in procedure.getEdges().toList()) {
        procedure.removeEdge(edge)
        val parts =
          if (edge.getAllLabels().any { needsSnapshot(it) }) edge.splitIf(::needsSnapshot)
          else listOf(edge)
        for (part in parts) {
          var operation = part
          var clear: XcfaLabel? = null
          val fence = part.getFlatLabels().singleOrNull()
          if (fence != null && needsSnapshot(fence)) {
            fence as FenceLabel
            val handle =
              handles.getOrPut(fence.lock.type) {
                Var("__theta_mutex_handle_${temporary++}", fence.lock.type).also {
                  procedure.addVar(it)
                }
              }
            clear =
              StmtLabel(
                Assign(handle.typed, handle.type.defaultValue.typed),
                metadata = fence.metadata,
              )
            val acquired =
              XcfaLocation("loc${XcfaLocation.uniqueCounter()}", metadata = part.metadata)
            // Keep address evaluation instrumentable without splitting the guarded ownership
            // update.
            val snapshot =
              StmtLabel(Assign(handle.typed, fence.lock.typed), metadata = fence.metadata)
            procedure.addEdge(part.withTarget(acquired).withLabel(SequenceLabel(listOf(snapshot))))
            operation = part.withSource(acquired).withLabel(fence.withLock(handle.ref))
          }
          replace(operation.label).forEach {
            val labels = if (clear == null) it else it + clear
            procedure.addEdge(operation.withLabel(SequenceLabel(labels, operation.label.metadata)))
          }
        }
      }
    }

    if (root != null) {
      prepend(root, initializers + StmtLabel(Assign(tids.getValue(root), Int(0))))
    } else {
      val bootstrap =
        XcfaProcedureBuilder(
          freshProcedureName(model, "__theta_mutex_init"),
          ProcedurePassManager(emptyList<List<ProcedurePass>>()),
        )
      bootstrap.createInitLoc()
      bootstrap.createFinalLoc()
      val starts =
        roots.mapIndexed { index, (procedure, args) ->
          val handle = Var("__theta_root_thread_$index", Int())
          bootstrap.addVar(handle)
          val params =
            procedure.getParams().mapIndexed { i, (param, _) ->
              if (param == tids.getValue(procedure)) Int(index)
              else args.getOrNull(i) ?: param.type.defaultValue
            }
          StartLabel(procedure.name, params, handle, EmptyMetaData)
        }
      bootstrap.addEdge(
        XcfaEdge(
          bootstrap.initLoc,
          bootstrap.finalLoc.get(),
          SequenceLabel(initializers + starts),
          EmptyMetaData,
        )
      )
      model.replaceEntryPoints(listOf(bootstrap to emptyList()))
    }
    procedures.forEach { it.checkEdgesHaveLocations(this) }
    entryCopy?.completeOptimizationPhase()
    return builder
  }

  private fun library(
    label: InvokeLabel,
    arrays: Map<Type, Arrays>,
    recursive: Boolean,
  ): List<List<XcfaLabel>> {
    if (!recursive) return listOf(emptyList())
    val address = label.params[1].address
    val flags = checkNotNull(arrays.getValue(address.type).recursive)
    fun set(value: Expr<BoolType>) =
      StmtLabel(Assign(flags, Write(flags.ref, address, value)), metadata = label.metadata)
    return when (label.name) {
      "pthread_mutexattr_init",
      "pthread_mutexattr_destroy" -> listOf(listOf(set(False())))
      "pthread_mutexattr_settype" -> {
        val type =
          checkNotNull((ExprUtils.simplify(label.params[2]) as? LitExpr<*>)?.intValue) {
            "Unknown mutex type: ${label.params[2]}"
          }
        listOf(
          listOf(set(if (MutexType.fromConstant(type) == MutexType.RECURSIVE) True() else False()))
        )
      }
      "pthread_mutex_init" -> {
        val attr = label.params[2].address
        val isNull = Eq(attr, attr.type.integerOf(0))
        val attrFlags = checkNotNull(arrays.getValue(attr.type).recursive)
        listOf(
          listOf(StmtLabel(Assume(isNull), metadata = label.metadata), set(False())),
          listOf(
            StmtLabel(Assume(Not(isNull)), metadata = label.metadata),
            set(Read(attrFlags.ref, attr)),
          ),
        )
      }
      else -> error("Not a mutex library operation: $label")
    }
  }

  private fun prepend(procedure: XcfaProcedureBuilder, labels: List<XcfaLabel>) {
    val init = procedure.initLoc
    val body = XcfaLocation("${init.name}__theta_mutex_body", metadata = init.metadata)
    procedure.addLoc(body)
    procedure
      .getEdges()
      .filter { it.source == init || it.target == init }
      .toList()
      .forEach {
        procedure.removeEdge(it)
        procedure.addEdge(
          XcfaEdge(
            if (it.source == init) body else it.source,
            if (it.target == init) body else it.target,
            it.label,
            it.metadata,
          )
        )
      }
    procedure.addEdge(XcfaEdge(init, body, SequenceLabel(labels), init.metadata))
  }

  private fun freshProcedureName(model: XcfaBuilder, prefix: String): String {
    var name = prefix
    while (model.getProcedures().any { it.name == name }) name = "${prefix}_${temporary++}"
    return name
  }

  private class Arrays(
    val simple: VarDecl<ArrayType<Type, IntType>>?,
    val recursive: VarDecl<ArrayType<Type, BoolType>>?,
    val acquisitions: VarDecl<ArrayType<Type, IntType>>?,
    val rw: VarDecl<ArrayType<Type, ArrayType<IntType, ArrayType<IntType, IntType>>>>?,
  ) {
    fun fence(label: FenceLabel, tid: Expr<IntType>): List<List<XcfaLabel>> {
      val h = label.lock.address
      fun assume(guard: Expr<BoolType>) = StmtLabel(Assume(guard), metadata = label.metadata)
      fun <T : Type> assign(v: VarDecl<T>, value: Expr<T>) =
        StmtLabel(Assign(v, value), metadata = label.metadata)
      if (label is MutexLockLabel || label is MutexTryLockLabel || label is MutexUnlockLabel) {
        val owners = checkNotNull(simple)
        val owner = Read(owners.ref, h)
        val own = Eq(owner, tid)
        val free = Eq(owner, Int(-1))
        val count = acquisitions?.let { Read(it.ref, h) }
        val canAcquire = recursive?.let { Or(free, And(Read(it.ref, h), own)) } ?: free
        val acquire =
          listOfNotNull(
            assume(canAcquire),
            assign(owners, Write(owners.ref, h, tid)),
            acquisitions?.let { assign(it, Write(it.ref, h, Inc(count!!))) },
          )
        return when (label) {
          is MutexLockLabel -> listOf(acquire)
          is MutexTryLockLabel -> {
            fun result(value: Int) =
              assign(label.successVar.typed, label.successVar.type.integerOf(value).typed)
            when (label.successful) {
              true -> listOf(acquire + result(0))
              false -> listOf(listOf(assume(Not(canAcquire)), result(MutexTryLockLabel.EBUSY)))
              null ->
                listOf(
                  acquire + result(0),
                  listOf(assume(Not(canAcquire)), result(MutexTryLockLabel.EBUSY)),
                )
            }
          }
          else ->
            if (acquisitions == null)
              listOf(
                listOf(assume(own), assign(owners, Write(owners.ref, h, Int(-1)))),
                listOf(assume(Not(own))),
              )
            else
              listOf(
                listOf(
                  assume(And(own, Eq(count!!, Int(1)))),
                  assign(owners, Write(owners.ref, h, Int(-1))),
                  assign(acquisitions, Write(acquisitions.ref, h, Int(0))),
                ),
                listOf(
                  assume(And(own, Gt(count!!, Int(1)))),
                  assign(acquisitions, Write(acquisitions.ref, h, Dec(count))),
                ),
                listOf(assume(Not(own))),
              )
        }
      }
      val locks = checkNotNull(rw)
      val read = Read(Read(locks.ref, h), Int(0))
      val write = Read(Read(locks.ref, h), Int(1))
      val r = Read(read, tid)
      val w = Read(write, tid)
      fun update(mode: Expr<IntType>, value: Expr<IntType>) =
        assign(
          locks,
          Write(
            locks.ref,
            h,
            Write(Read(locks.ref, h), mode, Write(Read(Read(locks.ref, h), mode), tid, value)),
          ),
        )
      return when (label) {
        is RWLockReadLockLabel ->
          listOf(listOf(assume(Eq(write, emptyOwners)), update(Int(0), Inc(r))))
        is RWLockWriteLockLabel ->
          listOf(
            listOf(
              assume(And(Eq(read, emptyOwners), Eq(write, emptyOwners))),
              update(Int(1), Int(1)),
            )
          )
        is RWLockUnlockLabel ->
          listOf(false, true).flatMap { hasRead ->
            listOf(false, true).map { hasWrite ->
              listOfNotNull(
                assume(
                  And(
                    if (hasRead) Gt(r, Int(0)) else Eq(r, Int(0)),
                    if (hasWrite) Gt(w, Int(0)) else Eq(w, Int(0)),
                  )
                ),
                if (hasRead) update(Int(0), Dec(r)) else null,
                if (hasWrite) update(Int(1), Dec(w)) else null,
              )
            }
          }
        else -> error("Unsupported mutex operation: $label")
      }
    }
  }

  companion object {
    private fun <I : Type, E : Type> constant(index: I, value: LitExpr<E>) =
      ArrayLitExpr.of<I, E>(emptyList(), value, ArrayType.of(index, value.type))

    private val emptyOwners = constant(Int(), Int(0))

    @Suppress("UNCHECKED_CAST")
    private val Expr<*>.address: Expr<Type>
      get() = this as Expr<Type>

    @Suppress("UNCHECKED_CAST")
    private val Expr<*>.typed: Expr<Type>
      get() = this as Expr<Type>

    @Suppress("UNCHECKED_CAST")
    private val VarDecl<*>.typed: VarDecl<Type>
      get() = this as VarDecl<Type>
  }
}
