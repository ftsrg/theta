/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import tools.refinery.logic.literal.Literal
import tools.refinery.store.dse.transition.actions.ActionLiteral

class MonolithicToRefinery(private val monolithicExpr: MonolithicExpr) {
  fun getRefineryChecker(): RefineryChecker {
    var transExpr = monolithicExpr.transExpr
    while (transExpr !is OrExpr) {
      check(transExpr.ops.size == 1 && transExpr.ops.first().type == Bool()) {
        "Refinery checker requires a top-level disjunction as the transition relation."
      }
      transExpr = transExpr.ops.first() as Expr<BoolType>
    }
    val transitions = (transExpr as OrExpr).ops.map { it.flatten() }

    transitions.map { transition ->
      transition.ops
        .filter {
          !(it is EqExpr<*> &&
            (it.rightOp == PrimeExpr.of(it.leftOp) || it.leftOp == PrimeExpr.of(it.rightOp)))
        }
        .forEach { expr ->
          val lhs = mutableListOf<Literal>()
          val rhs = mutableListOf<ActionLiteral>()
          TODO()
        }
    }

    TODO()
  }

  private fun Expr<BoolType>.flatten(): AndExpr =
    when (this) {
      is AndExpr -> And(ops.flatMap { it.flatten().ops.filter { o -> o !is TrueExpr } })
      else -> And(listOf(this))
    }
}
