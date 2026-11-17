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
package hu.bme.mit.theta.xcfa.passes.memory

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Gt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.boundCell
import hu.bme.mit.theta.xcfa.utils.boundTarget
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * Lowers `calloc(n, s)` into `malloc(n * s)` plus a `memset(p, 0, n * s)`, so it runs before
 * [MallocFunctionPass], which mints the base and records the size, and before
 * [MemoryFunctionsPass], which spells out the zero-fill over the object's cells.
 *
 * The fill is inserted **after** the assignment that consumes the call, not at the call itself:
 * `calloc` returns `void *`, so at the call the destination has no pointee type and
 * [MemoryFunctionsPass] cannot know what a cell is, while the typed pointer the result is bound to
 * (`int *p = calloc(4, sizeof *p)`) carries the real `cType`.
 *
 * Under the byte-addressed model a cell is a byte whatever the pointee, so the fill goes right
 * after the call. Under the cell-per-value models a `calloc` whose result is never bound to a typed
 * pointer (a variable or a memory cell) cannot be laid out, and the build is retried under `bytes`
 * rather than handing back a block that is silently not zeroed. The fill is skipped when the
 * allocation failed.
 *
 * A `num * size` that does not fit in `size_t` describes no object, so such a call returns NULL
 * (C23 7.24.3.2) instead of allocating the wrapped-around product.
 */
class CallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  companion object {
    private val CALLOC = setOf("calloc", "__builtin_calloc")
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().mapNotNull { it.name }.toSet()

    // Phase 1 -- turn each `calloc` into the allocation, remembering what still needs zeroing.
    val pending = mutableListOf<Triple<Expr<*>, Expr<*>, Expr<*>>>()
    val mallocs = LinkedHashMap<InvokeLabel, Triple<Expr<*>, Expr<*>, Expr<*>>>()
    val overflowing = LinkedHashMap<InvokeLabel, Expr<BoolType>>()
    for (edge in LinkedHashSet(builder.getEdges())) {
      val labels = edge.getFlatLabels()
      if (labels.none { it is InvokeLabel && it.name in CALLOC && it.name !in defined }) continue
      var changed = false
      val out =
        labels.map { label ->
          val ok = label is InvokeLabel && label.name in CALLOC && label.name !in defined
          if (!ok) return@map label
          label as InvokeLabel
          if (label.params.size < 3) return@map label
          val ret = label.params[0]
          changed = true
          val overflow = overflows(label.params[1], label.params[2])
          if (overflow == True()) return@map nullResult(ret)
          val count = count(label.params[1], label.params[2])
          val zero = CComplexType.getType(label.params[2], parseContext).getValue("0")
          val malloc =
            InvokeLabel.retFirst("malloc", listOf(ret, count), label.metadata, label.tempLookup)
          if (overflow != False()) overflowing[malloc] = overflow
          if (parseContext.memoryModel.byteAddressed()) mallocs[malloc] = Triple(ret, zero, count)
          else pending.add(Triple(ret, zero, count))
          malloc
        }
      if (changed) {
        val flat = out.flatMap { if (it is SequenceLabel) it.labels else listOf(it) }
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(flat, edge.label.metadata)))
      }
    }
    // An overflowing product returns NULL; only the other branch allocates (and is zeroed below).
    for ((malloc, overflow) in overflowing) {
      val edge = builder.getEdges().first { e -> e.getFlatLabels().any { it === malloc } }
      val labels = edge.getFlatLabels()
      val at = labels.indexOfFirst { it === malloc }
      builder.removeEdge(edge)
      val before = location(edge)
      val after = location(edge)
      addEdge(builder, edge, edge.source, before, labels.subList(0, at))
      addEdge(builder, edge, before, after, listOf(assume(Not(overflow)), malloc))
      addEdge(builder, edge, before, after, listOf(assume(overflow), nullResult(malloc.params[0])))
      addEdge(builder, edge, after, edge.target, labels.subList(at + 1, labels.size))
    }
    // Under bytes a cell is a byte whatever the pointee: the fill goes right after the allocation.
    for ((malloc, fill) in mallocs) {
      val (ret, zero, count) = fill
      val edge = builder.getEdges().first { e -> e.getFlatLabels().any { it === malloc } }
      val labels = edge.getFlatLabels()
      builder.removeEdge(edge)
      fillUnlessNull(
        builder,
        edge,
        labels,
        labels.indexOfFirst { it === malloc } + 1,
        ret,
        zero,
        count,
      )
    }
    if (pending.isEmpty()) return builder

    // Phase 2 -- the binding `p = (T *) tmp` is usually on a LATER edge than the call, so the fill
    // is placed by scanning the whole procedure rather than the call's own label list.
    for ((ret, zero, count) in pending) {
      val filled =
        LinkedHashSet(builder.getEdges()).any { edge ->
          val labels = edge.getFlatLabels()
          val bound = { l: XcfaLabel -> (boundTarget(l, ret) ?: boundCell(l, ret)) }
          val at = labels.indexOfFirst { bound(it)?.let(::pointeeIsTyped) == true }
          if (at < 0) return@any false
          val target = bound(labels[at])!!
          builder.removeEdge(edge)
          fillUnlessNull(builder, edge, labels, at + 1, target, zero, count)
          true
        }
      if (!filled) {
        throw RequiresByteAddressedMemoryException(
          "calloc whose result is not bound to a typed pointer the cell-per-value models can zero"
        )
      }
    }
    return builder
  }

  /** Splits [edge] after [at] labels to zero [target], unless the allocation failed. */
  private fun fillUnlessNull(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    labels: List<XcfaLabel>,
    at: Int,
    target: Expr<*>,
    zero: Expr<*>,
    count: Expr<*>,
  ) {
    val before = location(edge)
    val after = location(edge)
    val nullValue = CComplexType.getType(target, parseContext).nullValue
    val memset =
      InvokeLabel.retFirst("memset", listOf(target, target, zero, count), EmptyMetaData, emptyMap())
    addEdge(builder, edge, edge.source, before, labels.subList(0, at))
    addEdge(builder, edge, before, after, listOf(assume(Neq(target, nullValue)), memset))
    addEdge(builder, edge, before, after, listOf(assume(Eq(target, nullValue))))
    addEdge(builder, edge, after, edge.target, labels.subList(at, labels.size))
  }

  private fun location(edge: XcfaEdge): XcfaLocation =
    XcfaLocation(
      "${edge.source.name}_calloc${XcfaLocation.uniqueCounter()}",
      metadata = edge.source.metadata,
    )

  /** An edge from [source] to [target] carrying [labels], with [edge]'s metadata. */
  private fun addEdge(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    source: XcfaLocation,
    target: XcfaLocation,
    labels: List<XcfaLabel>,
  ) {
    builder.addEdge(
      XcfaEdge(source, target, SequenceLabel(labels, edge.label.metadata), edge.metadata)
    )
  }

  private fun nullResult(ret: Expr<*>): XcfaLabel =
    AssignStmtLabel(ret as RefExpr<*>, CComplexType.getType(ret, parseContext).nullValue)

  /**
   * Whether `num * size` exceeds `SIZE_MAX`: folded to `true` or `false` when both are literals, a
   * `size != 0 && num > SIZE_MAX / size` check that cannot wrap otherwise.
   */
  private fun overflows(num: Expr<*>, size: Expr<*>): Expr<BoolType> {
    val sizeT = CComplexType.getUnsignedLong(parseContext)
    val sizeMax = BigInteger.ONE.shiftLeft(sizeT.width()) - BigInteger.ONE
    val n = literalValue(num)
    val s = literalValue(size)
    if (n != null && s != null) return if (n.multiply(s) > sizeMax) True() else False()
    val numT = cast(sizeT.castTo(num), sizeT.smtType)
    val sizeTExpr = cast(sizeT.castTo(size), sizeT.smtType)
    return And(
      Neq(sizeTExpr, sizeT.nullValue),
      Gt(numT, Div(sizeT.getValue(sizeMax.toString()), sizeTExpr)),
    )
  }

  @Suppress("UNCHECKED_CAST")
  private fun assume(cond: Expr<*>): XcfaLabel = StmtLabel(AssumeStmt.of(cond as Expr<BoolType>))

  /** Whether the frontend metadata gives this pointer a pointee we can lay out into cells. */
  private fun pointeeIsTyped(pointer: Expr<*>): Boolean =
    when (val type = CComplexType.getType(pointer, parseContext)) {
      is hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct -> true
      is hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray -> true
      is hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer ->
        type.embeddedType !is hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
      else -> false
    }

  /** `num * size` in bytes: folded when both are literals, a `size_t` product otherwise. */
  private fun count(num: Expr<*>, size: Expr<*>): Expr<*> {
    val n = literalValue(num)
    val s = literalValue(size)
    if (n != null && s != null) {
      return CComplexType.getType(num, parseContext).getValue(n.multiply(s).toString())
    }
    val sizeT = CComplexType.getUnsignedLong(parseContext)
    return Mul(cast(sizeT.castTo(num), sizeT.smtType), cast(sizeT.castTo(size), sizeT.smtType))
  }

  private fun literalValue(expr: Expr<*>): BigInteger? =
    when (val e = ExprUtils.simplify(expr)) {
      is IntLitExpr -> e.value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(e)
      else -> null
    }
}
