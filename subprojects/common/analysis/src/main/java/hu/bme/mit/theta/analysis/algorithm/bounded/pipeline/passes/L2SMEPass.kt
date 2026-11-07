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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.TransitionInvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.action
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.DirectionalMonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPassResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

/**
 * Liveness-to-safety transformation for MonolithicExpr. With a [MonolithicExpr.livenessWitness],
 * the saved state is the earlier state of its transition invariant, and its invariants are checked
 * along with the repetition of a state.
 */
class L2SMEPass<Pr : InvariantProof> : DirectionalMonolithicExprPass<Pr> {

  private lateinit var vars: List<VarDecl<*>>
  private lateinit var action: ExprAction
  private lateinit var savedVar: VarDecl<BoolType>
  private lateinit var saveMap: Map<VarDecl<*>, VarDecl<*>>
  private var undefinedBehavior: Expr<BoolType> = False()

  private fun reprEq(e1: Expr<*>, e2: Expr<*>) =
    if (e1.getType() is FpType) FpExprs.FpAssign(e1 as Expr<FpType>, e2 as Expr<FpType>)
    else Eq(e1, e2)

  override fun forward(monolithicExpr: MonolithicExpr): MonolithicExprPassResult<Pr> {
    savedVar = Decls.Var("__saved_", BoolType.getInstance())
    vars = monolithicExpr.vars
    action = monolithicExpr.action()
    saveMap = vars.associateWith { Decls.Var("__saved_" + it.name, it.type) }
    val savedInitExpr = And(vars.map { reprEq(it.ref, saveMap[it]!!.ref) }.toList())
    val oneIndexing = VarIndexingFactory.indexing(1)
    val witness = monolithicExpr.livenessWitness
    undefinedBehavior = witness?.undefinedBehavior ?: False()
    val saveList =
      listOf(reprEq(savedVar.ref, False())) +
        listOfNotNull(witness?.saveCondition) +
        saveMap.map { reprEq(ExprUtils.applyPrimes(it.value.ref, oneIndexing), it.key.ref) } +
        reprEq(ExprUtils.applyPrimes(savedVar.ref, oneIndexing), BoolExprs.True())
    val skipList =
      saveMap.values.map { it.ref }.map { reprEq(ExprUtils.applyPrimes(it, oneIndexing), it) } +
        reprEq(ExprUtils.applyPrimes(savedVar.ref, oneIndexing), savedVar.ref)
    val prop =
      saveMap.entries.fold(savedVar.ref as Expr<BoolType>) { acc, (key, value) ->
        And(acc, reprEq(key.ref, value.ref))
      }
    val repeated = And(prop, monolithicExpr.propExpr)
    val checked =
      witness?.let {
        // Without repeating a state, a run can be infinite only in an infinite state space
        check(it.anyPrev.values.all(saveMap::containsKey)) {
          "Transition invariant over variables not in the model: " +
            it.anyPrev.values.filterNot(saveMap::containsKey)
        }
        val earlier = it.anyPrev.mapValues { (_, decl) -> saveMap.getValue(decl) }
        // The saved state meets the save condition, which induction cannot know on its own
        val saved =
          And(
            ExprUtils.changeDecls(it.saveCondition, saveMap),
            ExprUtils.changeDecls(it.transitionInvariant, earlier),
          )
        And(it.stateInvariant, Not(it.undefinedBehavior), SmartBoolExprs.Imply(savedVar.ref, saved))
      }
    val newIndexing =
      saveMap.values
        .fold(monolithicExpr.transOffsetIndex) { acc, value -> acc.inc(value, 1) }
        .inc(savedVar, 1)

    return MonolithicExprPassResult(
      MonolithicExpr(
        initExpr = And(monolithicExpr.initExpr, Not(savedVar.ref), savedInitExpr),
        transExpr = And(monolithicExpr.transExpr, SmartBoolExprs.Or(And(skipList), And(saveList))),
        propExpr = if (checked == null) Not(repeated) else And(Not(repeated), checked),
        transOffsetIndex = newIndexing,
        ctrlVars =
          monolithicExpr.ctrlVars + monolithicExpr.ctrlVars.map { saveMap[it]!! } + savedVar,
      )
    )
  }

  /** Only keep decls in the valuation that are contained within the parameter */
  private fun Valuation.filterVars(vars: Collection<Decl<*>>): ImmutableValuation =
    ImmutableValuation.from(toMap().filter { it.key in vars })

  override fun backward(
    safetyResult: SafetyResult<Pr, Trace<ExplState, ExprAction>>
  ): MonolithicExprPassResult<Pr> {
    if (safetyResult.isSafe) {
      // The earlier state of a transition invariant is the saved one, so __saved_ holds
      val invariant =
        ExprUtils.simplify(
          safetyResult.proof.getInvariant(),
          ImmutableValuation.builder().put(savedVar, BoolExprs.True()).build(),
        )
      // Later passes and adapters use Pr only as an InvariantProof
      @Suppress("UNCHECKED_CAST") val proof = TransitionInvariantProof(invariant, saveMap) as Pr
      return MonolithicExprPassResult(SafetyResult.safe(proof, safetyResult.stats.orElse(null)))
    }
    if (!safetyResult.isUnsafe)
      return MonolithicExprPassResult(SafetyResult.unknown(safetyResult.stats.orElse(null)))
    val trace = safetyResult.asUnsafe().cex
    if (ExprUtils.simplify(undefinedBehavior, trace.states.last().`val`) == BoolExprs.True())
      return MonolithicExprPassResult(SafetyResult.unknown(safetyResult.stats.orElse(null)))
    val newStates = trace.states.map { ExplState.of(it.filterVars(vars)) }
    val hondaIndex = trace.states.indexOfLast { !(it.`val`.toMap()[savedVar] as BoolLitExpr).value }

    return MonolithicExprPassResult(
        SafetyResult.unsafe(Trace.of(newStates, trace.actions.map { action }), safetyResult.proof)
      )
      .copy(hondaIndex = hondaIndex)
  }
}

private fun Type.isFinite(): Boolean =
  when (this) {
    is BoolType,
    is BvType,
    is FpType -> true
    is ArrayType<*, *> -> indexType.isFinite() && elemType.isFinite()
    else -> false
  }
