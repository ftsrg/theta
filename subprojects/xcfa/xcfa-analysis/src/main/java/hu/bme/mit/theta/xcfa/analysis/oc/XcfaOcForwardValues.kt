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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import java.util.IdentityHashMap

/**
 * Over-approximated value sets of the constants of a single-threaded event graph, filled in while
 * the graph is built. Events are created in a topological order of program order, so a constant's
 * value only depends on constants created before it, and one forward pass gives the values the
 * fixpoint of [XcfaOcValueAnalysis] would. A null set means any value.
 */
internal class XcfaOcForwardValues(private val maxValues: Int = MAX_VALUES) {

  private val values = HashMap<ConstDecl<*>, Set<LitExpr<*>>>()

  fun define(const: ConstDecl<*>, value: Set<LitExpr<*>>?) {
    if (value != null) values[const] = value
  }

  fun forget(const: ConstDecl<*>) {
    values.remove(const)
  }

  fun valueOf(const: ConstDecl<*>): Set<LitExpr<*>>? = values[const]

  /** The values of [expr], an expression over constants; [leaf] answers for anything else. */
  fun evaluate(
    expr: Expr<*>,
    leaf: (Expr<*>) -> Set<LitExpr<*>>? = { null },
    memo: IdentityHashMap<Expr<*>, Set<LitExpr<*>>?> = IdentityHashMap(),
  ): Set<LitExpr<*>>? {
    if (memo.containsKey(expr)) return memo[expr]
    val result =
      when {
        expr is LitExpr<*> -> setOf(expr)
        expr is RefExpr<*> && expr.decl is ConstDecl<*> -> valueOf(expr.decl as ConstDecl<*>)
        expr is RefExpr<*> || expr.ops.isEmpty() -> leaf(expr)
        else -> combine(expr, expr.ops.map { evaluate(it, leaf, memo) })
      }
    memo[expr] = result
    return result
  }

  /** The values of [expr] given the values of its operands. */
  fun combine(expr: Expr<*>, ops: List<Set<LitExpr<*>>?>): Set<LitExpr<*>>? =
    when (expr) {
      is OrExpr ->
        if (ops.any { it == TRUE }) TRUE
        else
          booleans(ops.any { it == null || True() in it }, ops.all { it == null || False() in it })
      is AndExpr ->
        if (ops.any { it == FALSE }) FALSE
        else
          booleans(ops.all { it == null || True() in it }, ops.any { it == null || False() in it })
      is NotExpr -> ops[0]?.let { booleans(False() in it, True() in it) }
      is IteExpr<*> ->
        when (ops[0]) {
          TRUE -> ops[1]
          FALSE -> ops[2]
          else -> union(ops[1], ops[2])
        }
      else -> enumerate(expr, ops)
    }?.takeIf { it.isNotEmpty() && it.size <= maxValues }

  private fun enumerate(expr: Expr<*>, ops: List<Set<LitExpr<*>>?>): Set<LitExpr<*>>? {
    if (ops.any { it == null }) return null
    val domains = ops.map { it!!.toList() }
    if (domains.fold(1L) { size, d -> size * d.size } > maxValues) return null
    val result = LinkedHashSet<LitExpr<*>>()
    val choice = IntArray(domains.size)
    try {
      while (true) {
        val args = domains.mapIndexed { i, d -> d[choice[i]] }
        result.add(expr.withOps(args).eval(ImmutableValuation.empty()))
        var i = 0
        while (i < choice.size && ++choice[i] == domains[i].size) choice[i++] = 0
        if (i == choice.size) return result
      }
    } catch (_: RuntimeException) {
      // e.g. a division by zero: the expression has no value to fold
      return null
    }
  }

  companion object {
    const val MAX_VALUES = 64

    val TRUE: Set<LitExpr<*>> = setOf(True())
    val FALSE: Set<LitExpr<*>> = setOf(False())

    fun union(a: Set<LitExpr<*>>?, b: Set<LitExpr<*>>?): Set<LitExpr<*>>? =
      if (a == null || b == null) null else a + b

    private fun booleans(canBeTrue: Boolean, canBeFalse: Boolean): Set<LitExpr<*>> =
      when {
        canBeTrue && canBeFalse -> setOf(True(), False())
        canBeTrue -> TRUE
        canBeFalse -> FALSE
        else -> setOf()
      }
  }
}
