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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.FlatAddressSpace
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.model.getObjExtentVar
import hu.bme.mit.theta.xcfa.model.getObjHeapVar
import hu.bme.mit.theta.xcfa.model.isGhostArrayInit
import hu.bme.mit.theta.xcfa.model.writeGhost

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
 * The type of the block an allocation's result [ret] is bound to in this procedure: the pointee of
 * the typed pointer variable or memory cell (`n->next = (T *) tmp`) it is stored into, or null when
 * there is none or it points to `void`.
 */
fun XcfaProcedureBuilder.boundPointee(parseContext: ParseContext, ret: Expr<*>): CComplexType? {
  val target =
    getEdges().firstNotNullOfOrNull { e ->
      e.getFlatLabels().firstNotNullOfOrNull { boundTarget(it, ret) ?: boundCell(it, ret) }
    } ?: return null
  val type = runCatching { CComplexType.getType(target, parseContext) }.getOrNull()
  val pointee = (type as? CPointer)?.embeddedType ?: return null
  return pointee.takeIf { it !is CVoid }
}

/**
 * The value [label] stores an allocation's result [ret] into memory as, or null. The value, not the
 * cell: the frontend converts it to the cell's pointer type, while the cell's own recorded type is
 * its address.
 */
private fun boundCell(label: XcfaLabel, ret: Expr<*>): Expr<*>? {
  val stmt = (label as? StmtLabel)?.stmt as? MemoryAssignStmt<*, *, *> ?: return null
  if (ret !is RefExpr<*> || ExprUtils.getVars(stmt.expr).none { it == ret.decl }) return null
  return stmt.expr
}

/**
 * The cells a `malloc` of [bytes] spans under flat addressing: whole elements of the typed pointer
 * its result [ret] is bound to, each one [CStruct.inlineCells] cells, or for a struct ending in a
 * flexible array member its header and the whole trailing elements. Null when there is no such
 * pointer, or its pointee is flexible elsewhere; the byte count, never fewer than the cells, then
 * stays the bound, which can miss an overrun but not invent one.
 */
fun XcfaProcedureBuilder.mallocCells(
  parseContext: ParseContext,
  ret: Expr<*>,
  bytes: Expr<*>,
): Expr<*>? {
  val pointee = boundPointee(parseContext, ret) ?: return null
  if (pointee is CArray) return null
  flexibleMemberCells(parseContext, pointee, bytes)?.let {
    return it
  }
  if (hasFlexibleMember(pointee)) return null
  val elementBytes = ObjectLayout.cellModelSize(pointee, true)
  val elementCells = CStruct.inlineCells(pointee)
  if (elementBytes == 1 && elementCells == 1) return bytes
  val type = CComplexType.getType(bytes, parseContext)
  val count = Div(type.castTo(bytes), type.getValue("$elementBytes"))
  return if (elementCells == 1) count else Mul(count, type.getValue("$elementCells"))
}

/** [mallocCells] of a struct whose last member, and only that, is a flexible array. */
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
