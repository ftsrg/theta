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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mul
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
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
 * pointer cannot be laid out, and the build is retried under `bytes` rather than handing back a
 * block that is silently not zeroed.
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
          val ret = label.params[0]
          val count = count(label.params[1], label.params[2])
          val zero = CComplexType.getType(label.params[2], parseContext).getValue("0")
          changed = true
          val malloc = InvokeLabel("malloc", listOf(ret, count), label.metadata, label.tempLookup)
          if (parseContext.memoryModel.byteAddressed()) {
            val memset =
              InvokeLabel("memset", listOf(ret, ret, zero, count), EmptyMetaData, emptyMap())
            return@map SequenceLabel(listOf(malloc, memset))
          }
          pending.add(Triple(ret, zero, count))
          malloc
        }
      if (changed) {
        val flat = out.flatMap { if (it is SequenceLabel) it.labels else listOf(it) }
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(flat, edge.label.metadata)))
      }
    }
    if (pending.isEmpty()) return builder

    // Phase 2 -- the binding `p = (T *) tmp` is usually on a LATER edge than the call, so the fill
    // is placed by scanning the whole procedure rather than the call's own label list.
    for ((ret, zero, count) in pending) {
      var placed = false
      for (edge in LinkedHashSet(builder.getEdges())) {
        val labels = edge.getFlatLabels()
        var inserted = false
        val out = mutableListOf<XcfaLabel>()
        for (label in labels) {
          out.add(label)
          if (inserted) continue
          val target = boundTarget(label, ret) ?: continue
          if (!pointeeIsTyped(target)) continue
          out.add(
            InvokeLabel("memset", listOf(target, target, zero, count), EmptyMetaData, emptyMap())
          )
          inserted = true
        }
        if (inserted) {
          builder.removeEdge(edge)
          builder.addEdge(edge.withLabel(SequenceLabel(out, edge.label.metadata)))
          placed = true
          break
        }
      }
      if (!placed) {
        throw RequiresByteAddressedMemoryException(
          "calloc whose result is not bound to a typed pointer the cell-per-value models can zero"
        )
      }
    }
    return builder
  }

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
