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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel

/** Marks a sub-object of a heap block: allocated like `alloca`, but not released at return. */
const val HEAP_SUBOBJECT = "__theta_heap_subobject"

/**
 * The cell layout of objects under the cell models, and the allocation of their sub-objects.
 *
 * An aggregate member or element is a separate object whose base lives in a cell of its parent (or
 * under [CStruct.inlinesAggregates], only a union is). Only these allocations create that object,
 * so every parent needs them, whether it lives on the stack (`alloca` markers, released at return)
 * or on the heap ([HEAP_SUBOBJECT] markers, which live as long as the block).
 */
class SubObjects(private val parseContext: ParseContext) {

  /**
   * Gives a struct object [target] a fresh runtime base, and recursively every sub-object it holds.
   * A struct's value is its base id, so a constant base would be shared by every activation of the
   * procedure; a base drawn from the runtime counter is distinct per allocation, as C requires.
   */
  fun allocateStruct(
    target: Expr<*>,
    type: CStruct,
    labels: MutableList<XcfaLabel>,
    marker: String = "alloca",
  ) {
    if (parseContext.memoryModel.byteAddressed()) {
      // One object of the struct's bytes: nested aggregates are regions of it, not objects.
      labels.add(alloca(target, staticUnits(type, 1).toInt(), marker))
      return
    }
    labels.add(alloca(target, if (type.isUnion) unionCellCount(type) else type.unitCount, marker))
    if (type.isUnion) return
    allocateMembers(target, type, type, 0, labels, marker)
  }

  /**
   * Allocates the sub-objects held by the [type] object at cell [first] of [target], an object of
   * [parentType].
   */
  fun allocateMembers(
    target: Expr<*>,
    parentType: CComplexType,
    type: CStruct,
    first: Int,
    labels: MutableList<XcfaLabel>,
    marker: String,
  ) {
    subObjectCells(type).forEach { (offset, fieldType) ->
      val cell = subobjectCell(target, parentType, first + offset, fieldType)
      allocateSubobject(cell, fieldType, labels, marker)
    }
  }

  /**
   * Gives an array object [target] a fresh runtime base, sized by the whole object (rows of a
   * multi-dimensional array live in the same block), and allocates its elements' sub-objects.
   */
  fun allocateArray(
    target: Expr<*>,
    type: CArray,
    labels: MutableList<XcfaLabel>,
    marker: String = "alloca",
  ) {
    val size =
      if (parseContext.memoryModel.byteAddressed())
        fixedArraySize(type)?.let { staticUnits(type.embeddedType, it.toLong()).toInt() }
      else flatArraySize(type)
    labels.add(alloca(target, size ?: return, marker))
    allocateArrayElements(target, type, labels, marker)
  }

  /**
   * Gives each element of [target] the objects it holds. Rows of `int a[3][4]` and elements of
   * `struct S a[3]` live inline in the array's cells (see `ExpressionVisitor#rowOf`) and need no
   * base; an aggregate *inside* an element, or a union element, does. An element of scalars, the
   * common case, allocates nothing however long the array is.
   */
  fun allocateArrayElements(
    target: Expr<*>,
    type: CArray,
    labels: MutableList<XcfaLabel>,
    marker: String = "alloca",
  ) {
    if (parseContext.memoryModel.byteAddressed()) return // elements are regions of the array
    val size = fixedArraySize(type) ?: return
    var leaf: CComplexType = type
    while (leaf is CArray) leaf = leaf.embeddedType
    if (leaf is CStruct && leaf.isUnion) {
      // A union element is a cell holding its object's base, as a union member of a struct is.
      for (index in 0 until (flatArraySize(type) ?: return)) {
        allocateStruct(subobjectCell(target, type, index, leaf), leaf, labels, marker)
      }
      return
    }
    val elementType = type.embeddedType
    if (elementType !is CStruct || elementType.isUnion) return
    for (index in 0 until size) {
      allocateMembers(target, type, elementType, index * elementType.unitCount, labels, marker)
    }
  }

  private fun allocateSubobject(
    cell: Expr<*>,
    type: CComplexType,
    labels: MutableList<XcfaLabel>,
    marker: String,
  ) {
    when (type) {
      is CStruct -> allocateStruct(cell, type, labels, marker)
      is CArray -> allocateArray(cell, type, labels, marker)
      else -> {} // a scalar field lives in its parent's cell; it needs no object of its own
    }
  }

  /**
   * Emits the `alloca(target, size)` marker [hu.bme.mit.theta.xcfa.passes.AllocaFunctionPass]
   * lowers into a fresh runtime base, recording the size under memsafety. The target may be a
   * variable or a memory cell.
   */
  private fun alloca(target: Expr<*>, size: Int, marker: String): XcfaLabel =
    InvokeLabel(
      marker,
      listOf(target, Fitsall(null, parseContext).getValue("$size")),
      metadata = EmptyMetaData,
    )

  /**
   * The cells of [type] that hold the base of a sub-object, with the sub-object's type: every
   * aggregate field, or under [CStruct.inlinesAggregates] only the unions, found through the inline
   * structs and arrays around them.
   */
  fun subObjectCells(type: CStruct): List<Pair<Int, CComplexType>> {
    if (!type.inlinesAggregates()) {
      return type.fields
        .filter { it.get2() is CStruct || it.get2() is CArray }
        .map { type.unitOffsetOf(it.get1()) to it.get2() }
    }
    fun walk(t: CComplexType, offset: Int): List<Pair<Int, CComplexType>> =
      when {
        t is CStruct && t.isUnion -> listOf(offset to t)
        t is CStruct -> t.fields.flatMap { walk(it.get2(), offset + t.unitOffsetOf(it.get1())) }
        t is CArray -> {
          val count = ObjectLayout.constantDimension(t) ?: 0
          val stride = CStruct.inlineCells(t.embeddedType)
          (0 until count).flatMap { walk(t.embeddedType, offset + it * stride) }
        }
        else -> listOf()
      }
    return walk(type, 0)
  }

  /**
   * The cell `arrays[parent][index]` a subobject (struct field, array element) lives at.
   *
   * When [parent] is itself an offset into an object -- `a[i]` on an array of structs is `a + i*k`,
   * see `ExpressionVisitor#rowOf` -- the two offsets are added and the *object* stays the base, so
   * the cell is `arrays[a][i*k + index]`. Leaving the sum in the base position would name a
   * different object, and `ReferenceElimination` expects a plain variable there.
   */
  fun subobjectCell(
    parent: Expr<*>,
    parentType: CComplexType,
    index: Int,
    subobjectType: CComplexType,
  ): Dereference<*, *, *> {
    val indexValue = parentType.getValue("$index")
    val sum = parent.withoutPos() as? AddExpr<*>
    val base = sum?.let { pointerOperandOf(it) }
    return if (base == null) {
        Dereference(cast(parent, parent.type), cast(indexValue, parent.type), subobjectType.smtType)
      } else {
        val offsets = sum.ops.filter { it.withoutPos() !== base } + indexValue
        Dereference(
          cast(base, base.type),
          cast(AbstractExprs.Add(offsets.map { cast(it, base.type) }), base.type),
          subobjectType.smtType,
        )
      }
      .also { parseContext.metadata.create(it, "cType", subobjectType) }
  }

  private fun Expr<*>.withoutPos(): Expr<*> = if (this is PosExpr<*>) op.withoutPos() else this

  /** The pointer/array operand of a sum, i.e. the object the rest of it is an offset into. */
  private fun pointerOperandOf(sum: AddExpr<*>): Expr<*>? =
    sum.ops
      .map { it.withoutPos() }
      .firstOrNull {
        val type = runCatching { CComplexType.getType(it, parseContext) }.getOrNull()
        type is CPointer || type is CArray || (type is CStruct && type.inlinesAggregates())
      }

  /**
   * An array's constant element count, or null for a flexible array member or a variable-length
   * array, whose elements then get no per-element allocation.
   */
  fun fixedArraySize(type: CArray): Int? {
    val dimension = type.arrayDimension ?: return null
    return when (val bounds = ExprUtils.simplify(dimension.expression)) {
      is IntLitExpr -> bounds.value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(bounds).toInt()
      else -> null
    }
  }

  /**
   * The number of cells an array occupies. An array is contiguous, so the element's own cell count
   * multiplies through: `int a[3][4]` is twelve cells addressed as `arrays[a][i*4 + j]`, and
   * `struct S a[3]` with a two-cell `S` is six, addressed as `arrays[a][i*2 + f]`. Null when a
   * dimension is not a compile-time constant.
   */
  fun flatArraySize(type: CArray): Int? {
    val size = fixedArraySize(type) ?: return null
    return when (val elementType = type.embeddedType) {
      is CArray -> flatArraySize(elementType)?.let { size * it }
      // A struct element occupies its own cells inline rather than a single cell holding a base --
      // see ExpressionVisitor#rowOf. A union keeps one cell: its members all share offset 0.
      is CStruct -> if (elementType.isUnion) size else size * elementType.unitCount
      else -> size
    }
  }

  /**
   * How many cells a union occupies: the single placeholder cell every word-sliceable union gets,
   * or -- for a byte-laid-out one ([CStruct.unionCellWidth] null) -- its real [ObjectLayout] size
   * in bytes, the granularity `ExpressionVisitor` addresses it at. It sizes the allocation and
   * `__theta_ptr_size`, so it must track that arithmetic exactly.
   */
  fun unionCellCount(type: CStruct): Int =
    if (type.unionCellWidth() == null) ObjectLayout.of(type, parseContext.architecture).bitSize / 8
    else 1

  /**
   * How many address units [count] consecutive objects of [type] span: bytes under the bytes model,
   * cells otherwise.
   */
  fun staticUnits(type: CComplexType, count: Long): Long =
    if (parseContext.memoryModel.byteAddressed())
      count * ((ObjectLayout.sizeBits(type, parseContext.architecture) + 7) / 8)
    else count * cellsOf(type)

  /**
   * How many storage cells one value of [type] occupies; mirrors `ExpressionVisitor#cellCountExpr`.
   */
  fun cellsOf(type: CComplexType): Int =
    when (type) {
      is CArray -> flatArraySize(type) ?: 1
      is CStruct -> if (type.isUnion) unionCellCount(type) else type.unitCount
      else -> 1
    }
}
