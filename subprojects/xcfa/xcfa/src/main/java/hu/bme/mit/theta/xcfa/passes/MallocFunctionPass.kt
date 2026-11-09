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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.FlatAddressSpace
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.HEAP_SUBOBJECT
import hu.bme.mit.theta.xcfa.utils.POINTER_BASE_CLASSES
import hu.bme.mit.theta.xcfa.utils.SubObjects
import hu.bme.mit.theta.xcfa.utils.boundPointee
import hu.bme.mit.theta.xcfa.utils.bumpAllocate
import hu.bme.mit.theta.xcfa.utils.ensureMallocVar
import hu.bme.mit.theta.xcfa.utils.firstAllocationRetType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.mallocVar
import hu.bme.mit.theta.xcfa.utils.memsafetyBound

private const val REALLOCATES = "reallocates"

private const val FREES = "frees"

/** The local flag choosing whether an allocation fails. */
private const val FAILS = "__theta_alloc_fails"

/** The most elements of a struct with sub-objects one `malloc` allocates them for. */
private const val MAX_HEAP_ELEMENTS = 64

/**
 * Transforms `malloc` into an address assignment out of the shared allocation counter, in the heap
 * residue class (see `POINTER_BASE_CLASSES`).
 *
 * Under flat addressing a block is instead the next slot of the address line, sized by the request
 * (see `bumpAllocate`). Memsafety records the size in the unit accesses index in: bytes under the
 * bytes model, else whole elements in cells (see `memsafetyBound`).
 *
 * `realloc` is handled here too, as an **in-place resize**: the returned pointer keeps the old base
 * and the object's size becomes the new one. A program must use realloc's return value whether or
 * not the block moved, so returning the same base preserves the observable contents exactly and
 * still gives the new bound to the memsafety size domain. What it does not model is the
 * invalidation of the old pointer, the same imprecision the analysis already has around frees;
 * `realloc(NULL, n)` and `realloc(q, 0)` are likewise left as the in-place resize. Under flat
 * addressing a block is grown in place, so when the program reallocates at all every heap block
 * reserves at least [FlatAddressSpace.UNKNOWN_EXTENT] units; only growth beyond that overlaps the
 * blocks allocated after it.
 *
 * A block of a struct type gets the sub-objects its cells hold (see [SubObjects]), as a stack
 * object does, for each element when its size is a constant. When that is impossible -- the block
 * is untyped, its element count is not constant, it ends in a flexible array member, or it is
 * reallocated -- and the program reaches sub-objects at all, the multi model refuses and the
 * program is rebuilt under flat, which lays them out inline. The same holds for a block whose first
 * member is a sub-object when the program frees memory. The type is the one the result is first
 * bound to; a block later used as an unrelated struct type is not covered.
 *
 * Either call may also fail and return NULL (C11 7.22.3), leaving a reallocated block intact.
 *
 * Requires the ProcedureBuilder be `deterministic`.
 */
class MallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val mallocVar = builder.parent.mallocVar(parseContext)
    checkNotNull(builder.metaData["deterministic"])
    reallocates(builder.parent)
    // Seed the counter before the snapshot below is taken: doing it mid-loop invalidates the
    // snapshot's init-procedure edges (see ensureMallocVar).
    builder.firstAllocationRetType(parseContext, this::isMalloc)?.let {
      builder.parent.ensureMallocVar(parseContext, it)
    }
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach { e ->
          val head = (e.label as SequenceLabel).labels[0]
          if (!predicate(head)) {
            builder.addEdge(e)
            return@forEach
          }
          val invokeLabel = head as InvokeLabel
          val labels =
            if (isMalloc(invokeLabel)) allocate(builder, invokeLabel, mallocVar)
            else reallocate(builder, invokeLabel)
          // Branches must start with an assume, so the outcome is a havoced flag.
          val fails = failureFlag(builder)
          val choice =
            XcfaLocation(
              "${e.source.name}_malloc${XcfaLocation.uniqueCounter()}",
              metadata = e.source.metadata,
            )
          val havoc = StmtLabel(HavocStmt.of(fails))
          builder.addEdge(XcfaEdge(e.source, choice, SequenceLabel(listOf(havoc)), e.metadata))
          val succeed = listOf(StmtLabel(Assume(Not(fails.ref)))) + labels
          builder.addEdge(XcfaEdge(choice, e.target, SequenceLabel(succeed), e.metadata))
          val fail = listOf(StmtLabel(Assume(fails.ref))) + fail(invokeLabel)
          builder.addEdge(XcfaEdge(choice, e.target, SequenceLabel(fail), e.metadata))
        }
      }
    }
    return builder
  }

  private fun allocate(
    builder: XcfaProcedureBuilder,
    invokeLabel: InvokeLabel,
    mallocVar: VarDecl<*>,
  ): List<XcfaLabel> {
    val ret = invokeLabel.params[0] as RefExpr<*>
    val arg = invokeLabel.params[1]
    val sizeLabels =
      (if (parseContext.isCheckMemsafety)
        listOf(
          builder.parent.allocate(parseContext, ret, builder.memsafetyBound(parseContext, ret, arg))
        )
      else listOf()) + subObjects(builder, ret, arg)
    if (parseContext.memoryModel.flatAddressing()) {
      val reserved =
        if (reallocates(builder.parent)) {
          val type = CComplexType.getType(arg, parseContext)
          val minimum = type.getValue(FlatAddressSpace.UNKNOWN_EXTENT.toString())
          Ite<Type>(Gt(type.castTo(arg), minimum), type.castTo(arg), minimum)
        } else arg
      return builder.parent.bumpAllocate(parseContext, ret, reserved, heap = true) + sizeLabels
    }
    val bump =
      AssignStmtLabel(
        mallocVar,
        Add(
          mallocVar.ref,
          CComplexType.getType(ret, parseContext).getValue("$POINTER_BASE_CLASSES"),
        ),
        ret.type,
        EmptyMetaData,
      )
    val assignRet = AssignStmtLabel(ret, cast(mallocVar.ref, ret.type))
    return listOf(bump, assignRet) + sizeLabels
  }

  private fun reallocate(builder: XcfaProcedureBuilder, invokeLabel: InvokeLabel): List<XcfaLabel> {
    val ret = invokeLabel.params[0] as RefExpr<*>
    val oldPtr = invokeLabel.params[1]
    val newSize = invokeLabel.params[2]
    val keepBase = AssignStmtLabel(ret, cast(oldPtr, ret.type))
    builder.boundPointee(parseContext, ret).let {
      if (it == null || hasSubObjects(it)) refuseUnlessFlat("a reallocated block")
    }
    return if (parseContext.isCheckMemsafety) {
      listOf(
        keepBase,
        builder.parent.allocate(
          parseContext,
          ret,
          builder.memsafetyBound(parseContext, ret, newSize),
        ),
      )
    } else {
      listOf(keepBase)
    }
  }

  private fun failureFlag(builder: XcfaProcedureBuilder): VarDecl<BoolType> {
    val existing = builder.getVars().firstOrNull { it.name == FAILS }
    return if (existing != null) cast(existing, Bool())
    else Var(FAILS, Bool()).also(builder::addVar)
  }

  /** A failed allocation: NULL, leaving any reallocated block as it was. */
  private fun fail(invokeLabel: InvokeLabel): List<XcfaLabel> {
    val ret = invokeLabel.params[0] as RefExpr<*>
    return listOf(AssignStmtLabel(ret, CComplexType.getType(ret, parseContext).nullValue))
  }

  /**
   * Allocates the sub-objects of each element of the fresh block [ret] of [bytes], when it holds a
   * struct that has any.
   */
  private fun subObjects(
    builder: XcfaProcedureBuilder,
    ret: Expr<*>,
    bytes: Expr<*>,
  ): List<XcfaLabel> {
    if (parseContext.memoryModel.byteAddressed()) return listOf()
    val pointee = builder.boundPointee(parseContext, ret)
    if (pointee == null) {
      refuseUnlessFlat("a block of unknown type")
      return listOf()
    }
    if (!hasSubObjects(pointee)) return listOf()
    val struct = pointee as? CStruct
    val count = struct?.let { elementCount(bytes, it) }
    if (struct == null || count == null) {
      refuseUnlessFlat(if (struct == null) "a block of arrays" else "a block of unknown length")
      return listOf()
    }
    val layout = SubObjects(parseContext)
    if (
      layout.subObjectCells(struct).any { (_, t) ->
        t is CArray && layout.fixedArraySize(t) == null
      }
    ) {
      refuseUnlessFlat("a flexible array member")
      return listOf()
    }
    if (layout.subObjectCells(struct).any { it.first == 0 }) refuseFirstMemberIfFreed(builder)
    val labels = mutableListOf<XcfaLabel>()
    for (index in 0 until count) {
      layout.allocateMembers(ret, struct, struct, index * struct.unitCount, labels, HEAP_SUBOBJECT)
    }
    return labels
  }

  /**
   * A sub-object at cell 0 has a base of its own, but in C its address is the block's: freeing it
   * frees the block, which the free check would report as invalid. Flat lays the member out inline,
   * and bytes also a union, which flat keeps as a sub-object.
   */
  private fun refuseFirstMemberIfFreed(builder: XcfaProcedureBuilder) {
    if (!parseContext.isCheckMemsafety || !parseContext.isAggregateMemberUsed) return
    if (!frees(builder.parent)) return
    val what = "a freed block whose first member is a separate object"
    if (parseContext.memoryModel.flatAddressing()) throw RequiresByteAddressedMemoryException(what)
    throw UnsupportedPointerSplitException("Unsupported heap sub-objects: $what")
  }

  private fun hasSubObjects(type: CComplexType): Boolean =
    when (type) {
      is CStruct -> !type.isUnion && SubObjects(parseContext).subObjectCells(type).isNotEmpty()
      is CArray ->
        hasSubObjects(type.embeddedType) || (type.embeddedType as? CStruct)?.isUnion == true
      else -> false
    }

  /** How many [struct] elements a constant [bytes] holds, or null if not constant or too many. */
  private fun elementCount(bytes: Expr<*>, struct: CStruct): Int? {
    val value =
      when (val size = ExprUtils.simplify(bytes)) {
        is IntLitExpr -> size.value
        is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(size)
        else -> return null
      }
    val count = value.toLong() / ObjectLayout.sizeofBytes(struct, parseContext.architecture)
    return count.takeIf { it <= MAX_HEAP_ELEMENTS }?.toInt()
  }

  /**
   * Hands a block whose sub-objects cannot be allocated to `--memory-model flat`, when sub-objects
   * are reached at all. Flat lays aggregates out inline, so only its unions are sub-objects; those
   * stay unallocated there, as before.
   */
  private fun refuseUnlessFlat(what: String) {
    if (parseContext.memoryModel.flatAddressing() || !parseContext.isAggregateMemberUsed) return
    throw UnsupportedPointerSplitException("Unsupported heap sub-objects: $what")
  }

  /** Whether any procedure calls `free`. */
  private fun frees(xcfa: XcfaBuilder): Boolean =
    xcfa.metaData.getOrPut(FREES) {
      xcfa.getProcedures().any { proc ->
        proc.getEdges().any { edge ->
          edge.getFlatLabels().any { it is InvokeLabel && it.name == "free" }
        }
      }
    } as Boolean

  /** Whether any procedure calls `realloc`, decided before the first one is rewritten. */
  private fun reallocates(xcfa: XcfaBuilder): Boolean =
    xcfa.metaData.getOrPut(REALLOCATES) {
      xcfa.getProcedures().any { proc ->
        proc.getEdges().any { edge ->
          edge.getFlatLabels().any { it is InvokeLabel && it.name == "realloc" }
        }
      }
    } as Boolean

  private fun isMalloc(it: XcfaLabel): Boolean = it is InvokeLabel && it.name == "malloc"

  private fun predicate(it: XcfaLabel): Boolean =
    it is InvokeLabel && (it.name == "malloc" || it.name == "realloc")
}
