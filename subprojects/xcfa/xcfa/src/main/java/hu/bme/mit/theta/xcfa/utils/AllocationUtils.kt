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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr
import hu.bme.mit.theta.core.type.abstracttype.GtExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.abstracttype.LtExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.FlatAddressSpace
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.model.getObjExtentVar
import hu.bme.mit.theta.xcfa.model.getObjHeapVar
import hu.bme.mit.theta.xcfa.model.isGhostArrayInit
import hu.bme.mit.theta.xcfa.model.writeGhost
import hu.bme.mit.theta.xcfa.passes.UnsupportedPointerSplitException
import java.math.BigInteger

/**
 * The number of pointer-base residue classes: every memory object has a base id, and the id modulo
 * this says what kind of object it is.
 *
 * | residue | kind                         | minted by                                       |
 * |---------|------------------------------|-------------------------------------------------|
 * | `3k+0`  | heap (`malloc`, `calloc`)    | `MallocFunctionPass`, from [mallocVar]          |
 * | `3k+1`  | static objects, and `alloca` | the frontend builder, then `AllocaFunctionPass` |
 * | `3k+2`  | address-taken locals         | `ReferenceElimination`                          |
 *
 * The classes never overlap. Both runtime kinds take their ids from the single [mallocVar] counter,
 * which advances by 3 per allocation so each allocation consumes its own `k`, and
 * `ReferenceElimination` has a compile-time counter of its own in a class no runtime allocation
 * uses. The one class with two producers is `3k+1`, where the counter is seeded past the frontend's
 * last compile-time base (see [ALLOCATION_STATIC_BASE_LIMIT]).
 *
 * The distinction matters to memsafety: `MemsafetyPass` accepts a `free` only of `3k+0` and its
 * memcleanup scan enumerates only `3k+0`, so a block the program is not responsible for freeing --
 * an `alloca`, a local's address -- must not be in that class.
 *
 * Under flat addressing none of this applies: there are no ids, every runtime object takes the next
 * slot from [bumpAllocate], and memsafety records heap blocks in a ghost array instead.
 */
const val POINTER_BASE_CLASSES = 3

/**
 * [XcfaBuilder.metaData] key under which the frontend publishes the first compile-time base id it
 * did *not* hand out to a static object. Absent means no compile-time bases were minted.
 */
const val ALLOCATION_STATIC_BASE_LIMIT = "staticBaseLimit"

private val mallocVars: MutableMap<XcfaBuilder, VarDecl<*>> = mutableMapOf()

/**
 * The shared allocation counter. `malloc` and `alloca` hand out addresses from the same one, so
 * that a heap block and a stack block can never be given the same base.
 */
fun XcfaBuilder.mallocVar(parseContext: ParseContext): VarDecl<*> =
  mallocVars.getOrPut(this) { Var("__malloc", CPointer(null, null, parseContext).smtType) }

/**
 * Where the allocation counter starts: past every static object. Under the multi model that is the
 * smallest multiple of three at or above the compile-time high-water mark; under flat addressing it
 * is the end of the static address space, which this seals.
 */
private fun XcfaBuilder.allocationSeed(parseContext: ParseContext): String {
  if (parseContext.memoryModel.flatAddressing()) {
    return parseContext.flatAddressSpace.end().toString()
  }
  val limit = (metaData[ALLOCATION_STATIC_BASE_LIMIT] as? Int) ?: 0
  return (((limit + POINTER_BASE_CLASSES - 1) / POINTER_BASE_CLASSES) * POINTER_BASE_CLASSES)
    .toString()
}

/**
 * Creates the shared allocation counter and seeds it in the init procedure, once per XCFA. Does
 * nothing if the counter already exists.
 *
 * Must be called *before* a pass starts iterating a snapshot of its own edges: seeding replaces
 * every outgoing edge of the init procedure's `initLoc`, so an edge captured beforehand is stale
 * and removing it later fails.
 */
fun XcfaBuilder.ensureMallocVar(parseContext: ParseContext, retType: CComplexType) {
  val mallocVar = mallocVar(parseContext)
  if (getVars().any { it.wrappedVar == mallocVar }) return
  val seed = retType.getValue(allocationSeed(parseContext))
  addVar(XcfaGlobalVar(mallocVar, seed, atomic = true))
  val initProc = getInitProcedures().map { it.first }
  check(initProc.size == 1) { "Multiple start procedure are not handled well" }
  val initAssign = StmtLabel(Assign(cast(mallocVar, mallocVar.type), cast(seed, mallocVar.type)))
  val staticSlots = staticSlotRegistrations(parseContext)
  initProc.forEach { proc ->
    val oldEdges = proc.initLoc.outgoingEdges.toList()
    val newEdges =
      oldEdges.map {
        it.withLabel(
          SequenceLabel(
            listOf(initAssign) +
              it.label.getFlatLabels().after(staticSlots) { l -> l.isGhostArrayInit() },
            it.label.metadata,
          )
        )
      }
    oldEdges.forEach(proc::removeEdge)
    newEdges.forEach(proc::addEdge)
  }
}

/**
 * Hands [target] (a variable or a memory cell) the next runtime slot of the flat address line, of
 * [size] address units: `target = __malloc; __malloc += size + GAP`. Under bitvector arithmetic a
 * bump that would wrap around is assumed not to happen, as the block could not exist.
 *
 * Under memsafety the slot's extent is recorded (see [getObjExtentVar]), and a heap block is marked
 * as such so that only it may be freed.
 */
fun XcfaBuilder.bumpAllocate(
  parseContext: ParseContext,
  target: Expr<*>,
  size: Expr<*>,
  heap: Boolean,
): List<XcfaLabel> {
  val mallocVar = mallocVar(parseContext)
  val pointerType = CComplexType.getType(target, parseContext)
  val extent =
    Add(cast(pointerType.castTo(size), mallocVar.type), cast(gap(pointerType), mallocVar.type))
  val labels =
    mutableListOf<XcfaLabel>(
      AssignStmtLabel(target, cast(mallocVar.ref, target.type)),
      AssignStmtLabel(mallocVar, Add(mallocVar.ref, extent), mallocVar.type, EmptyMetaData),
    )
  if (mallocVar.type !is IntType) {
    labels.add(StmtLabel(Assume(Gt(mallocVar.ref, cast(target, mallocVar.type)))))
  }
  labels.addAll(registerSlot(parseContext, target, extent, heap))
  return labels
}

/**
 * The pointer an allocation's `void *` result [ret] is bound to by [label] (`p = (T *) tmp`), or
 * null. The frontend casts the result to the declared pointer type, so this matches on the result
 * being referenced rather than on the right-hand side being exactly it.
 */
fun boundTarget(label: XcfaLabel, ret: Expr<*>): Expr<*>? {
  val stmt = (label as? StmtLabel)?.stmt as? AssignStmt<*> ?: return null
  if (ret !is RefExpr<*>) return null
  if (ExprUtils.getVars(stmt.expr).none { it == ret.decl }) return null
  return stmt.varDecl.ref
}

/**
 * The type of the block an allocation's result [ret] is bound to: the pointee of the typed pointer
 * variable or memory cell (`n->next = (T *) tmp`) it is stored into, or null when there is none or
 * the bindings disagree (see [blockBinding]).
 */
fun XcfaProcedureBuilder.boundPointee(parseContext: ParseContext, ret: Expr<*>): CComplexType? =
  (blockBinding(parseContext, ret) as? BlockBinding.Typed)?.pointee

/** What [blockBinding] found out about the element type of a fresh block. */
sealed interface BlockBinding {
  /** Every typed binding of the block agrees on this pointee. */
  data class Typed(val pointee: CComplexType) : BlockBinding

  /** The block is never bound to a typed pointer and never reaches a use that could access it. */
  data object Unused : BlockBinding

  /** The bindings disagree, or the block reaches a use whose element type is not known. */
  data object Unknown : BlockBinding
}

/** Calls that take a block without accessing it, so they say nothing about its element type. */
private val NON_ACCESSING_CALLS = setOf("free", "realloc")

/**
 * The element type of the block an allocation's result [ret] holds. The value is followed through
 * `void *` variables, from a procedure's return value to the results of its calls, and from call
 * and thread-start arguments to the callee's parameters, so a wrapper such as `void *xmalloc(n)`
 * takes the type its callers bind the block to. The callees are still separate procedures here.
 */
fun XcfaProcedureBuilder.blockBinding(parseContext: ParseContext, ret: Expr<*>): BlockBinding {
  val start = (ret as? RefExpr<*>)?.decl as? VarDecl<*> ?: return BlockBinding.Unknown
  val globals = parent.getVars().map { it.wrappedVar }.toSet()
  val pointees = mutableListOf<CComplexType>()
  val seen = mutableSetOf<Pair<XcfaProcedureBuilder, VarDecl<*>>>()
  val work = ArrayDeque<Pair<XcfaProcedureBuilder, VarDecl<*>>>()
  fun follow(proc: XcfaProcedureBuilder, v: VarDecl<*>) {
    if (seen.add(proc to v)) work.add(proc to v)
  }
  // Records the value reaching [target]; false when [target] is not a pointer.
  fun reach(proc: XcfaProcedureBuilder, target: Expr<*>, decl: VarDecl<*>?): Boolean {
    val type = runCatching { CComplexType.getType(target, parseContext) }.getOrNull()
    val pointee = (type as? CPointer)?.embeddedType ?: return false
    when {
      pointee !is CVoid -> pointees.add(pointee)
      decl != null -> follow(proc, decl)
      else -> return false
    }
    return true
  }
  follow(this, start)
  while (work.isNotEmpty()) {
    val (proc, v) = work.removeFirst()
    if (proc.getParams().any { it.first == v && it.second == ParamDirection.OUT }) {
      val calls =
        parent.getProcedures().flatMap { caller ->
          caller.getEdges().flatMap { it.getAllLabels() }.map { caller to it }
        }
      // A thread's result is read through `pthread_join`, which this search does not follow.
      if (calls.any { (_, l) -> l is StartLabel && l.name == proc.name }) {
        return BlockBinding.Unknown
      }
      val results = calls.filter { (_, l) -> l is InvokeLabel && l.name == proc.name }
      if (results.isEmpty()) return BlockBinding.Unknown
      for ((caller, call) in results) {
        val result = ((call as InvokeLabel).params.firstOrNull() as? RefExpr<*>)?.decl
        if (result is VarDecl<*>) follow(caller, result) else return BlockBinding.Unknown
      }
    }
    val owners = if (v in globals) parent.getProcedures() else setOf(proc)
    for (owner in owners) {
      for (label in owner.getEdges().flatMap { it.getAllLabels() }) {
        if (!owner.knownUse(label, v, ::reach)) return BlockBinding.Unknown
      }
    }
  }
  val first = pointees.firstOrNull() ?: return BlockBinding.Unused
  val flat = parseContext.memoryModel.flatAddressing()
  val agree =
    pointees.all {
      it == first ||
        (isScalar(it) &&
          isScalar(first) &&
          ObjectLayout.cellModelSize(it, flat) == ObjectLayout.cellModelSize(first, flat))
    }
  return if (agree) BlockBinding.Typed(first) else BlockBinding.Unknown
}

/**
 * Whether [label] uses [v] only in a way [blockBinding] understands: it compares it, copies it to a
 * pointer (handed to [reach]), or passes it to a call. False when it accesses memory through [v].
 */
private fun XcfaProcedureBuilder.knownUse(
  label: XcfaLabel,
  v: VarDecl<*>,
  reach: (XcfaProcedureBuilder, Expr<*>, VarDecl<*>?) -> Boolean,
): Boolean =
  when (label) {
    is StmtLabel ->
      when (val stmt = label.stmt) {
        is AssumeStmt -> onlyCompared(stmt.cond, v)
        is AssignStmt<*> ->
          !reads(stmt.expr, v) ||
            (!accesses(stmt.expr, v) &&
              (reach(this, stmt.varDecl.ref, stmt.varDecl) || onlyCompared(stmt.expr, v)))
        is MemoryAssignStmt<*, *, *> ->
          !reads(stmt.deref, v) &&
            (!reads(stmt.expr, v) || (!accesses(stmt.expr, v) && reach(this, stmt.expr, null)))
        else -> v !in StmtUtils.getVars(stmt)
      }
    is InvokeLabel -> {
      val args = label.params.drop(argumentStart(label.name, label.params))
      args.none { reads(it, v) } ||
        (args.none { accesses(it, v) } &&
          (label.name in NON_ACCESSING_CALLS || passToCallee(label.name, label.params, v, reach)))
    }
    is StartLabel ->
      label.params.none { reads(it, v) } ||
        (label.params.none { accesses(it, v) } && passToCallee(label.name, label.params, v, reach))
    else -> true
  }

/**
 * Hands the arguments of a call of [name] that read [v] to the callee's parameters. False when the
 * callee is not a procedure of this XCFA or a parameter is not a pointer.
 */
private fun XcfaProcedureBuilder.passToCallee(
  name: String,
  params: List<Expr<*>>,
  v: VarDecl<*>,
  reach: (XcfaProcedureBuilder, Expr<*>, VarDecl<*>?) -> Boolean,
): Boolean {
  val callee = parent.getProcedures().find { it.name == name } ?: return false
  val calleeParams = callee.getParams()
  val start = argumentStart(name, params)
  return params.withIndex().all { (i, arg) ->
    if (i < start || !reads(arg, v)) return@all true
    val param = calleeParams.getOrNull(i + 1 - start) ?: return@all false
    param.second != ParamDirection.OUT && reach(callee, param.first.ref, param.first)
  }
}

/**
 * The index of the first argument in [params] of a call of [name]: 1 after the return slot, 0 for a
 * void procedure, whose calls pass no return slot (see `ProcedureInlining`).
 */
private fun XcfaProcedureBuilder.argumentStart(name: String, params: List<Expr<*>>): Int {
  val callee = parent.getProcedures().find { it.name == name } ?: return 1
  return if (callee.getParams().size == params.size + 1) 0 else 1
}

private fun reads(expr: Expr<*>, v: VarDecl<*>): Boolean = ExprUtils.getVars(expr).contains(v)

/** Whether [expr] accesses memory through [v] or takes the address of [v]. */
private fun accesses(expr: Expr<*>, v: VarDecl<*>): Boolean =
  when (expr) {
    is Dereference<*, *, *>,
    is Reference<*, *> -> reads(expr, v)
    else -> expr.ops.any { accesses(it, v) }
  }

/** Whether [expr] reads [v] only as a pointer value that is compared. */
private fun onlyCompared(expr: Expr<*>, v: VarDecl<*>, compared: Boolean = false): Boolean =
  when (expr) {
    is RefExpr<*> -> expr.decl != v || compared
    is Dereference<*, *, *>,
    is Reference<*, *> -> !reads(expr, v)
    else -> {
      val comparison =
        expr is EqExpr<*> ||
          expr is NeqExpr<*> ||
          expr is LtExpr<*> ||
          expr is LeqExpr<*> ||
          expr is GtExpr<*> ||
          expr is GeqExpr<*>
      expr.ops.all { onlyCompared(it, v, compared || comparison) }
    }
  }

private fun isScalar(type: CComplexType): Boolean = type !is CStruct && type !is CArray

/**
 * The value [label] stores an allocation's result [ret] into memory as, or null. The value, not the
 * cell: the frontend converts it to the cell's pointer type, while the cell's own recorded type is
 * its address.
 */
fun boundCell(label: XcfaLabel, ret: Expr<*>): Expr<*>? {
  val stmt = (label as? StmtLabel)?.stmt as? MemoryAssignStmt<*, *, *> ?: return null
  if (ret !is RefExpr<*> || ExprUtils.getVars(stmt.expr).none { it == ret.decl }) return null
  return stmt.expr
}

/**
 * The size memsafety records for a fresh block of [bytes] bound to [ret]: the bytes under the bytes
 * model, else its whole elements in cells ([allocationCells]), the unit accesses index in. A block
 * that cells cannot bound is refused, so that the program is rebuilt under bytes: its element type
 * is unknown, or it is not empty but holds no whole element (size 0 would mean it is freed).
 */
fun XcfaProcedureBuilder.memsafetyBound(
  parseContext: ParseContext,
  ret: Expr<*>,
  bytes: Expr<*>,
): Expr<*> {
  if (parseContext.memoryModel.byteAddressed()) return bytes
  val binding = blockBinding(parseContext, ret)
  if (binding == BlockBinding.Unused) return bytes
  // Stepping a pointer to a union is refused, so only a union's first cell is ever reached.
  if ((binding as? BlockBinding.Typed)?.pointee?.let(::containsUnion) == true) return bytes
  val cells =
    (binding as? BlockBinding.Typed)?.let { allocationCells(parseContext, it.pointee, bytes) }
      ?: throw RequiresByteAddressedMemoryException(
        "A block whose element type is not known cannot be bounded in cells."
      )
  if ((literalValue(bytes)?.signum() ?: 0) > 0 && literalValue(cells)?.signum() == 0) {
    throw RequiresByteAddressedMemoryException(
      "A block smaller than one element cannot be bounded in cells."
    )
  }
  return cells
}

/**
 * The cells a block of [bytes] holding [pointee] spans under the cell-per-value models: its whole
 * elements of `sizeof` bytes each, each [CStruct.inlineCells] cells, or under flat, for a struct
 * ending in a flexible array member, its header and the whole trailing elements. Null for an array
 * pointee, and for a flexible member that is not laid out inline.
 */
fun allocationCells(parseContext: ParseContext, pointee: CComplexType, bytes: Expr<*>): Expr<*>? {
  val flat = parseContext.memoryModel.flatAddressing()
  if (pointee is CArray) return null
  if (flat) {
    flexibleMemberCells(parseContext, pointee, bytes)?.let {
      return it
    }
  } else if (hasFlexibleMember(pointee)) {
    // Only the flat layout counts the trailing elements of a flexible member.
    throw UnsupportedPointerSplitException("allocation of a struct with a flexible array member")
  }
  if (hasFlexibleMember(pointee)) return null
  val elementBytes = ObjectLayout.cellModelSize(pointee, flat)
  val elementCells = CStruct.inlineCells(pointee)
  if (elementBytes == 1 && elementCells == 1) return bytes
  val type = CComplexType.getType(bytes, parseContext)
  literalValue(bytes)?.let {
    return type.getValue("${it / elementBytes.toBigInteger() * elementCells.toBigInteger()}")
  }
  val count = Div(type.castTo(bytes), type.getValue("$elementBytes"))
  return if (elementCells == 1) count else Mul(count, type.getValue("$elementCells"))
}

private fun literalValue(expr: Expr<*>): BigInteger? =
  when (val simplified = ExprUtils.simplify(expr)) {
    is IntLitExpr -> simplified.value
    is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(simplified)
    else -> null
  }

/** [allocationCells] of a struct whose last member, and only that, is a flexible array. */
private fun flexibleMemberCells(
  parseContext: ParseContext,
  pointee: CComplexType,
  bytes: Expr<*>,
): Expr<*>? {
  val struct = (pointee as? CStruct)?.takeIf { !it.isUnion } ?: return null
  val member =
    (struct.fields.lastOrNull()?.get2() as? CArray)?.takeIf {
      ObjectLayout.constantDimension(it) == null
    } ?: return null
  val element = member.embeddedType
  if (struct.fields.dropLast(1).any { hasFlexibleMember(it.get2()) } || hasFlexibleMember(element))
    return null
  val type = CComplexType.getType(bytes, parseContext)
  // The header's size is what `sizeof` gives the struct, which counts the member as nothing.
  val header = ObjectLayout.cellModelSize(struct, true)
  val elements =
    Div(
      Sub(type.castTo(bytes), type.getValue("$header")),
      type.getValue("${ObjectLayout.cellModelSize(element, true)}"),
    )
  return Add(
    type.getValue("${CStruct.inlineCells(struct)}"),
    Mul(elements, type.getValue("${CStruct.inlineCells(element)}")),
  )
}

/** A union's members overlap at offset 0, each spanning its own cells: no one count covers them. */
fun containsUnion(type: CComplexType): Boolean =
  when (type) {
    is CArray -> containsUnion(type.embeddedType)
    is CStruct -> type.isUnion || type.fields.any { containsUnion(it.get2()) }
    else -> false
  }

private fun hasFlexibleMember(type: CComplexType): Boolean =
  when (type) {
    is CArray ->
      ObjectLayout.constantDimension(type) == null || hasFlexibleMember(type.embeddedType)
    is CStruct -> !type.isUnion && type.fields.any { hasFlexibleMember(it.get2()) }
    else -> false
  }

/** [inserted] placed right after the last label matching [anchor], or first when none does. */
private fun List<XcfaLabel>.after(
  inserted: List<XcfaLabel>,
  anchor: (XcfaLabel) -> Boolean,
): List<XcfaLabel> {
  val at = indexOfLast(anchor) + 1
  return subList(0, at) + inserted + subList(at, size)
}

private fun gap(pointerType: CComplexType): Expr<*> =
  pointerType.getValue(FlatAddressSpace.GAP.toString())

/** Records slot `[start, start + extent)` for memsafety, if it is tracked. */
private fun XcfaBuilder.registerSlot(
  parseContext: ParseContext,
  start: Expr<*>,
  extent: Expr<*>,
  heap: Boolean,
): List<XcfaLabel> {
  val extentVar = getObjExtentVar() ?: return listOf()
  val fitsall = Fitsall(null, parseContext)
  return listOfNotNull(
    writeGhost(parseContext, extentVar, start, fitsall.castTo(extent)),
    if (heap) writeGhost(parseContext, getObjHeapVar()!!, start, fitsall.unitValue) else null,
  )
}

private fun XcfaBuilder.staticSlotRegistrations(parseContext: ParseContext): List<XcfaLabel> {
  if (!parseContext.memoryModel.flatAddressing() || getObjExtentVar() == null) return listOf()
  val pointerType = CPointer(null, null, parseContext)
  return parseContext.flatAddressSpace.slots().flatMap {
    registerSlot(
      parseContext,
      pointerType.getValue(it.start.toString()),
      pointerType.getValue(it.extent.toString()),
      false,
    )
  }
}

/**
 * The C type the first allocation call matching [predicate] writes its base into, or null when this
 * procedure performs no such allocation. Lets the counter be seeded before the rewrite loop,
 * without needing an allocation site in hand.
 */
fun XcfaProcedureBuilder.firstAllocationRetType(
  parseContext: ParseContext,
  predicate: (XcfaLabel) -> Boolean,
): CComplexType? =
  getEdges()
    .asSequence()
    .flatMap { it.getFlatLabels().asSequence() }
    .filter(predicate)
    .map { CComplexType.getType((it as InvokeLabel).params[0], parseContext) }
    .firstOrNull()
