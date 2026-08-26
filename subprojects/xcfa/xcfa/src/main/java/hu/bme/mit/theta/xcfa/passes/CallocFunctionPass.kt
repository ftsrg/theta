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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * `calloc`, which nothing modelled: it reached the analysis as a call to a procedure that does not
 * exist and brought it down with "No such method calloc".
 *
 * It is lowered into the two operations that already have careful implementations rather than being
 * open-coded: `calloc(n, s)` becomes `malloc(n * s)` plus a `memset(p, 0, n * s)`. This pass runs
 * before [MallocFunctionPass], which mints the base and records the size, and before
 * [MemoryFunctionsPass], which spells out the zero-fill over the object's cells.
 *
 * **Where the fill goes is the whole trick.** `calloc` returns `void *`, so at the call itself the
 * destination has no pointee type and [MemoryFunctionsPass] cannot know what a cell is -- a
 * `memset` emitted there gives up, and the task merely fails on `memset` instead of on `calloc`.
 * But the result is immediately bound to a properly typed pointer (`int *p = calloc(4, sizeof
 * *p)`), and *that* expression carries the real `cType` in the frontend metadata. So the fill is
 * inserted **after** the assignment that consumes the call, against the typed destination, where
 * the cell layout is known exactly.
 *
 * The count still has to be statically known, for the same reason `memset` insists on it: a
 * symbolic one wants a loop over a bound this cannot see. A `calloc` whose count is not known, or
 * whose result is not bound to a typed pointer in the same block, is left exactly as it was -- it
 * still fails loudly, which is much better than handing back a block that is silently not zeroed.
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
          break
        }
      }
    }
    return builder
  }

  /** The variable an `x := ret` assignment binds the call's result to, if this label is one. */
  private fun boundTarget(label: XcfaLabel, ret: Expr<*>): Expr<*>? {
    val stmt = (label as? StmtLabel)?.stmt as? AssignStmt<*> ?: return null
    if (ret !is RefExpr<*>) return null
    // The binding is `p = (int *) tmp`, not a bare `p = tmp` -- the frontend casts the `void *`
    // result to the declared pointer type -- so match on the result being *referenced* rather than
    // on the right-hand side being exactly it.
    if (ExprUtils.getVars(stmt.expr).none { it == ret.decl }) return null
    return stmt.varDecl.ref
  }

  /** Whether the frontend metadata gives this pointer a pointee we can lay out into cells. */
  private fun pointeeIsTyped(pointer: Expr<*>): Boolean =
    when (val type = CComplexType.getType(pointer, parseContext)) {
      is hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct -> true
      is hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray -> true
      is hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer ->
        type.embeddedType !is
          hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
      else -> false
    }

  private fun literalValue(expr: Expr<*>): BigInteger? =
    when (val e = ExprUtils.simplify(expr)) {
      is IntLitExpr -> e.value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(e)
      else -> null
    }
}
