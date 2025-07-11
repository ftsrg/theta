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
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.orderVarsFromRandomStartingPoints
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing

fun MonolithicExpr.orderVars(): List<VarDecl<*>> {
  val events = this.split().map { MonolithicExprEvent(it, this.transOffsetIndex) }.toSet()
  val orderedVars = orderVarsFromRandomStartingPoints(this.vars, events)
  return orderedVars
}

// Filters affected variables
class MonolithicExprEvent: Event {

  constructor(expr: Expr<BoolType>, transOffsetIndex: VarIndexing) {
    val vars = ExprUtils.getVars(expr)
    var sub = BasicSubstitution.builder()
    for (v in vars) {
      sub = sub.put(
        v.getConstDecl(transOffsetIndex.get(v)),
        v.getConstDecl(0).ref
      )
    }
    val identityRemovedExpr =
      ExprUtils.simplify(sub.build().apply(PathUtils.unfold(expr,0)))
    val remainingConstants = ExprUtils.getConstants(identityRemovedExpr)
    this.affectedVars = vars.filter { it.getConstDecl(0) in remainingConstants }.toSet()
  }

  private val affectedVars: Set<VarDecl<*>>

  override fun getAffectedVars(): Set<VarDecl<*>> = affectedVars

}


