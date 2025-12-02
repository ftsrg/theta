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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.ExprUtils.getVars
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

data class MonolithicExpr
@JvmOverloads
constructor(
  val initExpr: Expr<BoolType>,
  val transExpr: Expr<BoolType>,
  val propExpr: Expr<BoolType>,
  val transOffsetIndex: VarIndexing = VarIndexingFactory.indexing(1),
  val vars: List<VarDecl<*>> =
    (getVars(initExpr) union getVars(transExpr) union getVars(propExpr)).toList(),
  val ctrlVars: Collection<VarDecl<*>> = listOf(),
  val events: List<Event<VarDecl<*>>> =
    splitTransExpr(transExpr).map { MonolithicExprEvent(it, transOffsetIndex) },
) {
  val split: List<Expr<BoolType>> by lazy { splitTransExpr(transExpr) }
}

fun MonolithicExpr.action() =
  object : ExprAction {
    override fun toExpr(): Expr<BoolType> = transExpr

    override fun nextIndexing(): VarIndexing = transOffsetIndex
  }

// TODO: not this simple, can mess up STS with or
private fun splitTransExpr(expr: Expr<BoolType>): List<Expr<BoolType>> {
  val simplifiedTransExpr = ExprUtils.simplify(expr)
  return if (simplifiedTransExpr is OrExpr) {
    simplifiedTransExpr.ops
  } else listOf(simplifiedTransExpr)
}
