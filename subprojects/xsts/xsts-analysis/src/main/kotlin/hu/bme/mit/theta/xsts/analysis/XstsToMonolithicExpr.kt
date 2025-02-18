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

import com.google.common.base.Preconditions.checkArgument
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState

fun XSTS.toMonolithicExpr(): MonolithicExpr {

  val lastActionWasEnv = Decls.Var("__lastActionWasEnv__", BoolType.getInstance())
  val initialized = Decls.Var("__initialized__", BoolType.getInstance())
  val initControlVars = And(lastActionWasEnv.ref, Not(initialized.ref))

  val initExpr = And(this.initFormula, initControlVars)
  val propExpr = this.prop

  val monolithicTransition =
    IfStmt.of(
      Not(initialized.ref),
      SequenceStmt.of(
        ImmutableList.of(
          this.init,
          AssignStmt.of(initialized, True())
        )
      ),
      IfStmt.of(
        lastActionWasEnv.ref,
        SequenceStmt.of(
          ImmutableList.of(
            this.tran,
            AssignStmt.of(lastActionWasEnv, False())
          )
        ),
        SequenceStmt.of(
          ImmutableList.of(
            this.env,
            AssignStmt.of(lastActionWasEnv, True())
          )
        )
      )
    )
  val monolithicUnfoldResult = StmtUtils.toExpr(monolithicTransition, VarIndexingFactory.indexing(0))
  val transExpr = And(monolithicUnfoldResult.exprs)

  return MonolithicExpr(initExpr, transExpr, propExpr, monolithicUnfoldResult.indexing, VarIndexingFactory.indexing(0))
}

fun XSTS.valToAction(val1: Valuation, val2: Valuation): XstsAction {
  val val1Map = val1.toMap()
  val lastActionWasEnv1 = (val1Map[val1Map.keys.first { it.name == "__lastActionWasEnv__" }] as BoolLitExpr).value
  val initialized1 = (val1Map[val1Map.keys.first { it.name == "__initialized__" }] as BoolLitExpr).value

  val val2Map = val1.toMap()
  val lastActionWasEnv2 = (val2Map[val2Map.keys.first { it.name == "__lastActionWasEnv__" }] as BoolLitExpr).value
  val initialized2 = (val2Map[val2Map.keys.first { it.name == "__initialized__" }] as BoolLitExpr).value

  checkArgument(initialized2)
  checkArgument(lastActionWasEnv1 != lastActionWasEnv2)

  if(!initialized1) return XstsAction.create(this.init)
  else if(lastActionWasEnv1) return XstsAction.create(this.tran)
  else return XstsAction.create(this.env)
}

fun XSTS.valToState(val1: Valuation): XstsState<ExplState> {
  val valMap = val1.toMap()
  val lastActionWasEnv = (valMap[valMap.keys.first { it.name == "__lastActionWasEnv__" }] as BoolLitExpr).value
  val initialized = (valMap[valMap.keys.first { it.name == "__initialized__" }] as BoolLitExpr).value

  return XstsState.of(
    ExplState.of(val1),
    lastActionWasEnv,
    initialized
  )
}
