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
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import java.util.List

fun XSTS.toMonolithicExpr(): MonolithicExpr {

  val initStmtUnfoldResult = StmtUtils.toExpr(init, VarIndexingFactory.indexing(0))
  var initExpr = PathUtils.unfold(And(listOf(initFormula) + initStmtUnfoldResult.exprs), 0)
  val subBuilder = BasicSubstitution.builder()
  for (v in stateVars) {
    if (initStmtUnfoldResult.indexing.get(v) > 0) {
      for (i in 0..<initStmtUnfoldResult.indexing.get(v)) {
        subBuilder.put(v.getConstDecl(i), Decls.Var(v.name + "__MONOLITHIC_TEMP" + i, v.type).ref)
      }
    }
    subBuilder.put(v.getConstDecl(initStmtUnfoldResult.indexing.get(v)), v.ref)
  }
  initExpr = ExprUtils.simplify(subBuilder.build().apply(initExpr))
  val propExpr = this.prop

  val envOrig =
    if (env.stmts.size == 1 && env.stmts.get(0) is NonDetStmt) env.stmts[0] as NonDetStmt else env
  val tranOrig =
    if (tran.stmts.size == 1 && tran.stmts.get(0) is NonDetStmt) tran.stmts[0] as NonDetStmt
    else tran

  val monolithicTransition =
    NonDetStmt.of(
      envOrig.stmts
        .stream()
        .flatMap { e: Stmt ->
          tranOrig.stmts.stream().map { t: Stmt -> SequenceStmt.of(List.of(e, t)) as Stmt }
        }
        .toList()
    )
  val monolithicUnfoldResult =
    StmtUtils.toExpr(monolithicTransition, VarIndexingFactory.indexing(0))
  val transExpr = ExprUtils.simplify(And(monolithicUnfoldResult.exprs))

  return MonolithicExpr(
    initExpr,
    transExpr,
    propExpr,
    monolithicUnfoldResult.indexing,
    VarIndexingFactory.indexing(0),
    valToState = this::valToState,
    biValToAction = this::valToAction,
    ctrlVars = this.ctrlVars,
    vars = this.stateVars.toList(),
  )
}

fun XSTS.valToAction(val1: Valuation, val2: Valuation): XstsAction {
  return XstsAction.create(SequenceStmt.of(listOf(env, tran)))
}

fun XSTS.valToState(val1: Valuation): XstsState<ExplState> {
  return XstsState.of(ExplState.of(val1), false, true)
}
