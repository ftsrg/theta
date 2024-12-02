/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import java.util.HashMap

fun MonolithicExpr.createAbstract(prec: PredPrec): MonolithicExpr {
  // TODO: handle initOffsetIndex in abstract initExpr
  val lambdaList = ArrayList<IffExpr>()
  val lambdaPrimeList = ArrayList<IffExpr>()
  val activationLiterals = ArrayList<VarDecl<*>>()
  val literalToPred = HashMap<Decl<*>, Expr<BoolType>>()

  prec.preds.forEachIndexed { index, expr ->
    run {
      val v = Decls.Var("v$index", BoolType.getInstance())
      activationLiterals.add(v)
      literalToPred[v] = expr
      lambdaList.add(IffExpr.of(v.ref, expr))
      lambdaPrimeList.add(
        BoolExprs.Iff(Exprs.Prime(v.ref), ExprUtils.applyPrimes(expr, this.transOffsetIndex))
      )
    }
  }

  var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
  this.vars
    .filter { it !in ctrlVars }
    .forEach { decl ->
      repeat(transOffsetIndex.get(decl)) { indexingBuilder = indexingBuilder.inc(decl) }
    }

  return MonolithicExpr(
    initExpr = And(And(lambdaList), initExpr),
    transExpr = And(And(lambdaList), And(lambdaPrimeList), transExpr),
    propExpr = Not(And(And(lambdaList), Not(propExpr))),
    transOffsetIndex = indexingBuilder.build(),
    initOffsetIndex = VarIndexingFactory.indexing(0),
    vars = activationLiterals + ctrlVars,
    valToState = { valuation: Valuation ->
      PredState.of(
        valuation
          .toMap()
          .entries
          .stream()
          .filter { it.key !in ctrlVars }
          .map {
            when ((it.value as BoolLitExpr).value) {
              true -> literalToPred[it.key]
              false -> Not(literalToPred[it.key])
            }
          }
          .toList()
      )
    },
    biValToAction = this.biValToAction,
    ctrlVars = ctrlVars,
  )
}
