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
package hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState

fun XSTS.toMonolithicExpr(): MonolithicExpr {

  val initUnfoldResult = StmtUtils.toExpr(this.init, VarIndexingFactory.indexing(0))
  val initExpr = And(And(initUnfoldResult.exprs), this.initFormula)
  val initOffsetIndex = initUnfoldResult.indexing
  val envTran = Stmts.SequenceStmt(listOf(this.env, this.tran))
  val envTranUnfoldResult = StmtUtils.toExpr(envTran, VarIndexingFactory.indexing(0))
  val transExpr = And(envTranUnfoldResult.exprs)
  val transOffsetIndex = envTranUnfoldResult.indexing
  val propExpr = this.prop

  return MonolithicExpr(initExpr, transExpr, propExpr, transOffsetIndex, initOffsetIndex)
}

fun XSTS.valToAction(val1: Valuation, val2: Valuation): XstsAction {
  return XstsAction.create(Stmts.SequenceStmt(listOf(this.env, this.tran)))
}

fun XSTS.valToState(val1: Valuation): XstsState<ExplState> {
  return XstsState.of(ExplState.of(val1), false, true)
}
