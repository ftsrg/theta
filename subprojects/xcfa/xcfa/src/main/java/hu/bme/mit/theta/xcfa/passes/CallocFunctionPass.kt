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

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
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
 * The count has to be statically known, for the same reason `memset` insists on it. A `calloc`
 * whose count is not known is left as it was, and one whose result is not bound to a typed pointer
 * (a variable or a memory cell) is refused: failing loudly beats handing back a block that is
 * silently not zeroed. The fill is skipped when the allocation failed.
 */
class CallocFunctionPass(val parseContext: ParseContext) : ProcedurePass {

  companion object {
    private val CALLOC = setOf("calloc", "__builtin_calloc")
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().mapNotNull { it.name }.toSet()

    // Phase 1 -- turn each `calloc` into the allocation, remembering what still needs zeroing.
    val pending = mutableListOf<Triple<Expr<*>, Expr<*>, Expr<*>>>()
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
          val num = literalValue(label.params[1]) ?: return@map label
          val size = literalValue(label.params[2]) ?: return@map label
          val ret = label.params[0]
          val bytes = num.multiply(size)
          val count: Expr<*> =
            CComplexType.getType(label.params[1], parseContext).getValue(bytes.toString())
          val zero = CComplexType.getType(label.params[2], parseContext).getValue("0")
          pending.add(Triple(ret, zero, count))
          changed = true
          InvokeLabel("malloc", listOf(ret, count), label.metadata, label.tempLookup)
        }
      if (changed) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(out, edge.label.metadata)))
      }
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
        throw UnsupportedFrontendElementException(
          "Unsupported calloc: its result $ret is not bound to a typed pointer."
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
    val loc = {
      XcfaLocation(
        "${edge.source.name}_calloc${XcfaLocation.uniqueCounter()}",
        metadata = edge.source.metadata,
      )
    }
    val before = loc()
    val after = loc()
    val nullValue = CComplexType.getType(target, parseContext).nullValue
    val memset =
      InvokeLabel("memset", listOf(target, target, zero, count), EmptyMetaData, emptyMap())
    val add = { s: XcfaLocation, t: XcfaLocation, l: List<XcfaLabel> ->
      builder.addEdge(XcfaEdge(s, t, SequenceLabel(l, edge.label.metadata), edge.metadata))
    }
    add(edge.source, before, labels.subList(0, at))
    add(before, after, listOf(assume(Neq(target, nullValue)), memset))
    add(before, after, listOf(assume(Eq(target, nullValue))))
    add(after, edge.target, labels.subList(at, labels.size))
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

  private fun literalValue(expr: Expr<*>): BigInteger? =
    when (val e = ExprUtils.simplify(expr)) {
      is IntLitExpr -> e.value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(e)
      else -> null
    }
}
