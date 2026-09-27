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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
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

/** Implicit predicate abstraction over a [MonolithicExpr]. */
class ImplicitPredicateAbstractor(private val concreteModel: MonolithicExpr) {

  private val predToLiteral = LinkedHashMap<Expr<BoolType>, VarDecl<BoolType>>()
  private val literalToPredMap = LinkedHashMap<Decl<*>, Expr<BoolType>>()
  private val initCopies = LinkedHashMap<VarDecl<*>, VarDecl<*>>()
  private lateinit var currentPrec: PredPrec

  /** Builds the abstract [MonolithicExpr] for [prec]; reports which literals were newly created. */
  fun abstractModel(prec: PredPrec): AbstractionResult {
    currentPrec = prec
    val lambdaList = ArrayList<IffExpr>()
    val lambdaPrimeList = ArrayList<IffExpr>()
    val activationLiterals = ArrayList<VarDecl<*>>()
    val newLiterals = ArrayList<VarDecl<BoolType>>()

    // predicates over only ctrl vars get no literal
    prec.preds
      .filter { !concreteModel.ctrlVars.containsAll(ExprUtils.getVars(it)) }
      .forEach { expr ->
        val v =
          predToLiteral.getOrPut(expr) {
            val lit = Decls.Var("v${predToLiteral.size}", BoolType.getInstance())
            literalToPredMap[lit] = expr
            newLiterals.add(lit)
            lit
          }
        activationLiterals.add(v)
        lambdaList.add(IffExpr.of(v.ref, expr))
        lambdaPrimeList.add(
          BoolExprs.Iff(
            Exprs.Prime(v.ref),
            ExprUtils.applyPrimes(expr, concreteModel.transOffsetIndex),
          )
        )
      }

    val transExpr = And(And(lambdaList), And(lambdaPrimeList), concreteModel.transExpr)
    val isConcrete = { v: VarDecl<*> -> v !in concreteModel.ctrlVars && v !in activationLiterals }

    // All concrete vars, not only the state vars, get fresh constants in every step (offset one
    // above their concrete offset): steps may share only literals and ctrl vars.
    val concreteVars = (concreteModel.vars + ExprUtils.getVars(transExpr)).distinct()
    var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
    concreteVars.filter(isConcrete).forEach { decl ->
      repeat(concreteModel.transOffsetIndex[decl]) { indexingBuilder = indexingBuilder.inc(decl) }
    }
    val transOffsetIndex = indexingBuilder.build()

    // Init gets its own copies of the concrete vars; sharing them with the first step would make
    // the initial state stronger than its literals, which loop-free path checking cannot see.
    val initExpr = And(And(lambdaList), concreteModel.initExpr)
    val initRenaming =
      ExprUtils.getVars(initExpr).filter(isConcrete).associateWith {
        initCopies.getOrPut(it) { Decls.Var("__init_" + it.name, it.type) }
      }

    val model =
      MonolithicExpr(
        initExpr = ExprUtils.changeDecls(initExpr, initRenaming),
        transExpr = transExpr,
        propExpr = Not(And(And(lambdaList), Not(concreteModel.propExpr))),
        transOffsetIndex = transOffsetIndex,
        vars = activationLiterals + concreteModel.ctrlVars,
        ctrlVars = concreteModel.ctrlVars,
        events =
          concreteModel.events.map {
            val originalAffectedVars = it.getAffectedVars()
            val affectedCtrlVars = originalAffectedVars.filter { v -> v in concreteModel.ctrlVars }
            val affectedActivationLiterals =
              activationLiterals.filter { v ->
                literalToPredMap[v]!!.let { pred ->
                  ExprUtils.getVars(pred).any { v2 -> v2 in originalAffectedVars }
                }
              }
            object : Event<VarDecl<*>> {
              override fun getAffectedVars(): List<VarDecl<*>> =
                affectedCtrlVars + affectedActivationLiterals
            }
          },
      )
    return AbstractionResult(model, newLiterals)
  }

  /** Maps an abstract trace to a predicate trace under the prec of the last [abstractModel]. */
  fun toPredTrace(trace: Trace<ExplState, ExprAction>): Trace<PredState, ExprAction> =
    Trace.of(trace.states.map(this::toPredState), trace.actions.map { concreteModel.action() })

  private fun toPredState(valuation: Valuation): PredState =
    PredState.of(
      valuation.toMap().minus(concreteModel.ctrlVars.toSet()).map {
        when ((it.value as BoolLitExpr).value) {
          true -> literalToPredMap[it.key]
          false -> currentPrec.negate(literalToPredMap[it.key])
        }
      }
    )
}

data class AbstractionResult(
  val model: MonolithicExpr,
  val newLiterals: List<VarDecl<BoolType>>, // creation order
)
