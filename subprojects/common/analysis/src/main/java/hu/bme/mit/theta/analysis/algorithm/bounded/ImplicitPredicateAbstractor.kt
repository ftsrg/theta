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
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

/** Implicit predicate abstraction over a [MonolithicExpr], split by connected literals. */
class ImplicitPredicateAbstractor(private val concreteModel: MonolithicExpr) {

  private val predToLiteral = LinkedHashMap<Expr<BoolType>, VarDecl<BoolType>>()
  private val literalToPredMap = LinkedHashMap<Decl<*>, Expr<BoolType>>()
  private lateinit var currentPrec: PredPrec
  private var groupTransitions: List<List<Int>> = emptyList()

  private val transitionVars: List<Set<VarDecl<*>>> by lazy {
    concreteModel.split.map(::readWriteVars)
  }

  private val unfoldedTransitions: List<Expr<BoolType>> by lazy {
    concreteModel.split.map { PathUtils.unfold(it, VarIndexingFactory.indexing(0)) }
  }

  /** Builds the abstract [MonolithicExpr] for [prec]; reports which literals were newly created. */
  fun abstractModel(prec: PredPrec): AbstractionResult {
    currentPrec = prec
    val lambda = LinkedHashMap<VarDecl<BoolType>, Expr<BoolType>>()
    val lambdaPrime = LinkedHashMap<VarDecl<BoolType>, Expr<BoolType>>()
    val activationLiterals = ArrayList<VarDecl<BoolType>>()
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
        lambda[v] = IffExpr.of(v.ref, expr)
        lambdaPrime[v] =
          BoolExprs.Iff(
            Exprs.Prime(v.ref),
            ExprUtils.applyPrimes(expr, concreteModel.transOffsetIndex),
          )
      }

    var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
    concreteModel.vars.forEach { decl ->
      val offset = concreteModel.transOffsetIndex[decl]
      if (decl !in concreteModel.ctrlVars) {
        repeat(offset) { indexingBuilder = indexingBuilder.inc(decl) }
      } else if (offset > 1) {
        repeat(offset - 1) { indexingBuilder = indexingBuilder.inc(decl) }
      }
    }
    val transOffsetIndex = indexingBuilder.build()

    val literalVars = activationLiterals.associateWith { ExprUtils.getVars(literalToPredMap[it]!!) }
    val groups = LinkedHashMap<Set<VarDecl<BoolType>>, MutableList<Int>>()
    concreteModel.split.indices.forEach { i ->
      // literals sharing a variable with the transition or with another connected literal
      var reached: Set<VarDecl<*>> = transitionVars[i]
      do {
        val before = reached.size
        reached =
          reached + literalVars.values.filter { vars -> vars.any { it in reached } }.flatten()
      } while (reached.size > before)
      val connected =
        activationLiterals.filter { literalVars[it]!!.any { v -> v in reached } }.toSet()
      groups.getOrPut(connected) { ArrayList() }.add(i)
    }
    groupTransitions = groups.values.map { it.toList() }
    val splits =
      groups.map { (connected, transitions) ->
        val identity = activationLiterals.filter { it !in connected }
        And(
          listOf(
            And(connected.map { lambda[it]!! }),
            And(connected.map { lambdaPrime[it]!! }),
            Or(transitions.map { concreteModel.split[it] }),
            And(identity.map { Eq(Exprs.Prime(it.ref), it.ref) }),
          )
        )
      }
    val allLambda = And(lambda.values)

    val model =
      MonolithicExpr(
        initExpr = And(allLambda, concreteModel.initExpr),
        transExpr = if (splits.size == 1) splits[0] else Or(splits),
        propExpr = Not(And(allLambda, Not(concreteModel.propExpr))),
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
        explicitSplit = splits,
      )
    return AbstractionResult(model, newLiterals)
  }

  fun toPredTrace(trace: Trace<ExplState, ExprAction>): Trace<PredState, ExprAction> {
    val actions =
      trace.actions.mapIndexed { k, action ->
        if (action is MonolithicExprSplitAction && action.index in groupTransitions.indices)
          concreteAction(groupTransitions[action.index], trace.states[k], trace.states[k + 1])
        else concreteModel.action()
      }
    return Trace.of(trace.states.map(this::toPredState), actions)
  }

  private fun toPredState(valuation: Valuation): PredState =
    PredState.of(
      valuation.toMap().minus(concreteModel.ctrlVars.toSet()).map {
        when ((it.value as BoolLitExpr).value) {
          true -> literalToPredMap[it.key]
          false -> currentPrec.negate(literalToPredMap[it.key])
        }
      }
    )

  private fun concreteAction(
    candidates: List<Int>,
    source: ExplState,
    target: ExplState,
  ): ExprAction {
    val enabled = candidates.filter { ctrlConsistent(it, source.`val`, target.`val`) }
    val chosen = if (enabled.isEmpty()) candidates else enabled
    if (chosen.size == 1) return concreteModel.splitAction(chosen[0])
    val expr = Or(chosen.map { concreteModel.split[it] })
    return object : ExprAction {
      override fun toExpr(): Expr<BoolType> = expr

      override fun nextIndexing(): VarIndexing = concreteModel.transOffsetIndex
    }
  }

  @Suppress("UNCHECKED_CAST")
  private fun ctrlConsistent(transition: Int, source: Valuation, target: Valuation): Boolean {
    val builder = ImmutableValuation.builder()
    for (ctrl in concreteModel.ctrlVars) {
      source.eval(ctrl).ifPresent {
        builder.put(ctrl.getConstDecl(0) as Decl<Type>, it as LitExpr<Type>)
      }
      target.eval(ctrl).ifPresent {
        builder.put(
          ctrl.getConstDecl(concreteModel.transOffsetIndex[ctrl]) as Decl<Type>,
          it as LitExpr<Type>,
        )
      }
    }
    return ExprUtils.simplify(unfoldedTransitions[transition], builder.build()) !is FalseExpr
  }

  // a havoc leaves no constraint, so a variable the transition does not frame counts as written
  private fun readWriteVars(transition: Expr<BoolType>): Set<VarDecl<*>> {
    val mentioned = ExprUtils.getVars(transition)
    val havocked =
      concreteModel.vars.filter {
        it !in concreteModel.ctrlVars && concreteModel.transOffsetIndex[it] > 0 && it !in mentioned
      }
    val event = MonolithicExprEvent(transition, concreteModel.transOffsetIndex)
    return event.getAffectedVars().toSet() + havocked
  }
}

data class AbstractionResult(val model: MonolithicExpr, val newLiterals: List<VarDecl<BoolType>>)
