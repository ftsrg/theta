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

package hu.bme.mit.theta.analysis.algorithm.ic3

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
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

class AbstractHelper @JvmOverloads constructor(
    val traceCheckerFactory: (MonolithicExpr) -> ExprTraceChecker<ItpRefutation>,
    val initPrec: (MonolithicExpr) -> PredPrec = { monolithicExpr ->
      PredPrec.of(listOf(monolithicExpr.propExpr, monolithicExpr.initExpr))
    },
    val refine: (PredPrec, Expr<BoolType>) -> PredPrec = { prec, expr ->
      prec.join(PredPrec.of(expr))
    }
  )
{
  private lateinit var literalToPred: Map<Decl<*>, Expr<BoolType>>
  private lateinit var concreteModel: MonolithicExpr
  lateinit var currentPrec: PredPrec
  fun createPrec(monolithicExpr: MonolithicExpr): MonolithicExpr {
    concreteModel = monolithicExpr
    currentPrec = initPrec(concreteModel)
    val abstractModel = createAbstract(concreteModel, currentPrec)
    return abstractModel
  }

  fun createAbstract(model: MonolithicExpr, prec: PredPrec): MonolithicExpr {
    val lambdaList = ArrayList<IffExpr>()
    val lambdaPrimeList = ArrayList<IffExpr>()
    val activationLiterals = ArrayList<VarDecl<*>>()
    val literalToPred = HashMap<Decl<*>, Expr<BoolType>>()

    prec.preds
      .filter { !model.ctrlVars.containsAll(ExprUtils.getVars(it)) }
      .forEachIndexed { index, expr ->
        val v = Decls.Var("v$index", BoolType.getInstance())
        activationLiterals.add(v)
        literalToPred[v] = expr
        lambdaList.add(IffExpr.of(v.ref, expr))
        lambdaPrimeList.add(
          BoolExprs.Iff(Exprs.Prime(v.ref), ExprUtils.applyPrimes(expr, model.transOffsetIndex))
        )
      }

    this.literalToPred = literalToPred

    var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
    model.vars
      .filter { it !in model.ctrlVars }
      .forEach { decl ->
        repeat(model.transOffsetIndex[decl]) { indexingBuilder = indexingBuilder.inc(decl) }
      }
    val transOffsetIndex = indexingBuilder.build()
    return MonolithicExpr(
      initExpr = And(And(lambdaList), model.initExpr),
      transExpr = And(And(lambdaList), And(lambdaPrimeList), model.transExpr),
      propExpr = Not(And(And(lambdaList), Not(model.propExpr))),
      transOffsetIndex = transOffsetIndex,
      vars = activationLiterals + model.ctrlVars,
      ctrlVars = model.ctrlVars,
      events =
        model.events.map {
          val originalAffectedVars = it.getAffectedVars()
          val affectedCtrlVars = originalAffectedVars.filter { v -> v in model.ctrlVars }
          val affectedActivationLiterals =
            activationLiterals.filter { v ->
              literalToPred[v]!!.let { pred ->
                ExprUtils.getVars(pred).any { v2 -> v2 in originalAffectedVars }
              }
            }
          object : Event<VarDecl<*>> {
            override fun getAffectedVars(): List<VarDecl<*>> =
              affectedCtrlVars + affectedActivationLiterals
          }
        },
    )
  }
  fun getConcretisationResult(cex: Trace<ExplState, ExprAction>): ExprTraceStatus<ItpRefutation?>? {
    val trace =
      cex.let {
        Trace.of(
          it.states.map(this::activationLiteralsToPredicates),
          it.actions.map { concreteModel.action() },
        )
      }
    return traceCheckerFactory(concreteModel).check(trace)
  }
  fun activationLiteralsToPredicates(valuation: Valuation) =
    PredState.of(
      valuation.toMap().minus(concreteModel.ctrlVars.toSet()).map {
        when ((it.value as BoolLitExpr).value) {
          true -> literalToPred[it.key]
          false -> currentPrec.negate(literalToPred[it.key])
        }
      }
    )

}