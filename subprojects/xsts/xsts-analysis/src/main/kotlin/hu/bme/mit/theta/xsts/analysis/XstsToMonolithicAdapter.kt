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
package hu.bme.mit.theta.xsts.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.ProofConservingModelToMonolithicAdapter
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xsts.XSTS

class XstsToMonolithicAdapter(override val model: XSTS) :
  ProofConservingModelToMonolithicAdapter<XSTS, XstsState<out ExprState>, XstsAction> {

  override val monolithicExpr: MonolithicExpr
    get() {
      val initStmtUnfoldResult = StmtUtils.toExpr(model.init, VarIndexingFactory.indexing(0))
      var initExpr =
        PathUtils.unfold(And(listOf(model.initFormula) + initStmtUnfoldResult.exprs), 0)
      val subBuilder = BasicSubstitution.builder()
      for (v in model.stateVars) {
        if (initStmtUnfoldResult.indexing.get(v) > 0) {
          for (i in 0..<initStmtUnfoldResult.indexing.get(v)) {
            subBuilder.put(
              v.getConstDecl(i),
              Decls.Var(v.name + "__MONOLITHIC_TEMP" + i, v.type).ref,
            )
          }
        }
        subBuilder.put(v.getConstDecl(initStmtUnfoldResult.indexing.get(v)), v.ref)
      }
      initExpr = ExprUtils.simplify(subBuilder.build().apply(initExpr))
      val propExpr = model.prop

      val envOrig =
        if (model.env.stmts.size == 1 && model.env.stmts.get(0) is NonDetStmt)
          model.env.stmts[0] as NonDetStmt
        else model.env
      val tranOrig =
        if (model.tran.stmts.size == 1 && model.tran.stmts.get(0) is NonDetStmt)
          model.tran.stmts[0] as NonDetStmt
        else model.tran

      val monolithicTransition =
        NonDetStmt.of(
          envOrig.stmts
            .stream()
            .flatMap { e: Stmt ->
              tranOrig.stmts.stream().map { t: Stmt -> SequenceStmt.of(listOf(e, t)) as Stmt }
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
        ctrlVars = model.ctrlVars,
        vars = model.stateVars.toList(),
        events = xsts.events(),
      )
    }

  override fun traceToModelTrace(
    trace: Trace<ExplState, ExprAction>
  ): Trace<XstsState<out ExprState>, XstsAction> {
    val states = trace.states.map { valToState(it.`val`) }
    return Trace.of(states, XstsAction.create(SequenceStmt.of(listOf(model.env, model.tran))))
  }

  private fun valToState(valuation: Valuation): XstsState<ExplState> {
    return XstsState.of(ExplState.of(valuation), false, true)
  }
}
