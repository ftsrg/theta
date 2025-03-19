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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import java.util.*
import kotlin.collections.plus

/**
 * A checker for bounded model checking.
 *
 * @param <S> The state type, must inherit from ExprState.
 * @param <A> The action type, must inherit from StmtAction.
 * @param monolithicExpr The monolithic expression to be checked
 * @param shouldGiveUp A function determining whether to give up checking based on a given iteration
 *   count. Use this to implement custom timeout or thread interruption checking subroutines.
 * @param bmcSolver The solver for bounded model checking.
 * @param bmcEnabled A function determining whether bounded model checking is enabled. Cannot be
 *   disabled per-iteration. Use the capabilities of the lambda parameter to decide on enabledness
 *   based on external factors, such as available memory or time limit remaining.
 * @param lfPathOnly A function determining whether to consider only loop-free paths.
 * @param itpSolver The solver for interpolation, used in IMC.
 * @param imcEnabled A function determining whether IMC is enabled. Can be different per-iteration.
 * @param indSolver The solver for induction checking in KIND.
 * @param kindEnabled A function determining whether k-induction (KIND) is enabled.
 * @param valToState A function mapping valuations to expression states, used to construct a
 *   counterexample.
 * @param biValToAction A function mapping pairs of valuations to statements, used to construct a
 *   counterexample.
 * @param logger The logger for logging.
 * @param reverseTrace If 'true', reverse the trace in the counterexample.
 */
class BoundedChecker<S : ExprState, A : ExprAction>
@JvmOverloads
constructor(
  private val monolithicExpr: MonolithicExpr,
  private val shouldGiveUp: (Int) -> Boolean = { false },
  private val bmcSolver: Solver? = null,
  private val bmcEnabled: () -> Boolean = { bmcSolver != null },
  private val lfPathOnly: () -> Boolean = { true },
  private val itpSolver: ItpSolver? = null,
  private val imcEnabled: (Int) -> Boolean = { itpSolver != null },
  private val indSolver: Solver? = null,
  private val kindEnabled: (Int) -> Boolean = { indSolver != null },
  private val valToState: (Valuation) -> S,
  private val biValToAction: (Valuation, Valuation) -> A,
  private val logger: Logger,
  private val reverseTrace: Boolean = false,
  private val needProof: Boolean = false,
) : SafetyChecker<PredState, Trace<S, A>, UnitPrec> {

  private val vars = monolithicExpr.vars
  private val unfoldedInitExpr =
    PathUtils.unfold(monolithicExpr.initExpr, VarIndexingFactory.indexing(0))
  private val unfoldedPropExpr = { i: VarIndexing -> PathUtils.unfold(monolithicExpr.propExpr, i) }
  private val indices = mutableListOf(VarIndexingFactory.indexing(0))
  private val exprs = mutableListOf<Expr<BoolType>>()
  private var kindLastIterLookup = 0
  private var iteration = 0

  init {
    check(bmcSolver != itpSolver || bmcSolver == null) { "Use distinct solvers for BMC and IMC!" }
    check(bmcSolver != indSolver || bmcSolver == null) { "Use distinct solvers for BMC and KInd!" }
    check(itpSolver != indSolver || itpSolver == null) { "Use distinct solvers for IMC and KInd!" }
  }

  override fun check(prec: UnitPrec?): SafetyResult<PredState, Trace<S, A>> {

    iteration = 0

    val isBmcEnabled = bmcEnabled() // we don't allow per-iteration setting of bmc enabledness
    bmcSolver?.add(unfoldedInitExpr)

    while (!shouldGiveUp(iteration)) {
      iteration++
      logger.write(Logger.Level.MAINSTEP, "Starting iteration $iteration\n")
      if (!kindEnabled(iteration) && imcEnabled(iteration) && bmcEnabled()) {
        logger.writeln(
          Logger.Level.INFO,
          "BMC and IMC together are inefficient; IMC includes BMC as a substep.",
        )
      }
      check((!kindEnabled(iteration)) || bmcEnabled()) {
        "K-Induction needs BMC as an external substep."
      }

      exprs.add(PathUtils.unfold(monolithicExpr.transExpr, indices.last()))

      indices.add(indices.last().add(monolithicExpr.transOffsetIndex))

      if (isBmcEnabled) {
        bmc()?.let {
          return it
        }
      }

      if (kindEnabled(iteration)) {
        if (!isBmcEnabled) {
          error("Bad configuration: induction check should always be preceded by a BMC/SAT check")
        }
        kind()?.let {
          return it
        }
        kindLastIterLookup = iteration
      }

      if (imcEnabled(iteration)) {
        itp()?.let {
          return it
        }
      }
    }
    return SafetyResult.unknown(BoundedStatistics(iteration))
  }

  private fun bmc(): SafetyResult<PredState, Trace<S, A>>? {
    val bmcSolver = this.bmcSolver!!
    logger.write(Logger.Level.MAINSTEP, "\tStarting BMC\n")

    if (iteration == 1) {
      WithPushPop(bmcSolver).use {
        bmcSolver.add(Not(unfoldedPropExpr(indices.first())))

        if (bmcSolver.check().isSat) {
          val trace = getTrace(bmcSolver.model)
          logger.write(
            Logger.Level.MAINSTEP,
            "CeX found in the initial state (length ${trace.length()})\n",
          )
          return SafetyResult.unsafe(trace, PredState.of(), BoundedStatistics(iteration))
        }
      }
    }

    bmcSolver.add(exprs.last())

    if (lfPathOnly()) { // indices contains currIndex as last()
      val loopfree = LinkedList<Expr<BoolType>>()
      for (indexing in indices) {
        if (indexing != indices.last()) {
          val allVarsSame =
            And(
              vars.map {
                Eq(PathUtils.unfold(it.ref, indexing), PathUtils.unfold(it.ref, indices.last()))
              }
            )
          loopfree += Not(allVarsSame)
        }
      }
      bmcSolver.add(loopfree)

      if (bmcSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in BMC step\n")
        val proof =
          if (needProof) {
            // we enumerate all states explored by previous iteration of BMC
            val expr =
              And(
                exprs.subList(0, exprs.size - 1) +
                  //                  loopfree.subList(0, loopfree.size - 1) +
                  unfoldedInitExpr
              )
            extractModel(expr, indices.subList(0, indices.size - 1))
          } else {
            True()
          }
        return SafetyResult.safe(PredState.of(proof), BoundedStatistics(iteration))
      }
    }

    return WithPushPop(bmcSolver).use {
      bmcSolver.add(Not(unfoldedPropExpr(indices.last())))

      if (bmcSolver.check().isSat) {
        val trace = getTrace(bmcSolver.model)
        logger.write(Logger.Level.MAINSTEP, "CeX found in BMC step (length ${trace.length()})\n")
        SafetyResult.unsafe(trace, PredState.of(), BoundedStatistics(iteration))
      } else null
    }
  }

  private fun kind(): SafetyResult<PredState, Trace<S, A>>? {
    val indSolver = this.indSolver!!

    logger.write(Logger.Level.MAINSTEP, "\tStarting k-induction\n")

    exprs.subList(kindLastIterLookup, exprs.size).forEach { indSolver.add(it) }
    val allSafe = LinkedList<Expr<BoolType>>()
    indices.subList(kindLastIterLookup, indices.size - 1).forEach {
      allSafe.add(unfoldedPropExpr(it))
    }
    indSolver.add(allSafe)

    return WithPushPop(indSolver).use {
      indSolver.add(Not(unfoldedPropExpr(indices.last())))

      if (indSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in k-induction step\n")
        val proof =
          if (needProof) {
            val bmc = And(exprs + unfoldedInitExpr)
            val kindExprs = LinkedList<Expr<BoolType>>()
            val kindIndices =
              LinkedList(listOf(indices.last().add(monolithicExpr.transOffsetIndex)))
            for (i in (0 until iteration)) {
              kindExprs.add(PathUtils.unfold(monolithicExpr.transExpr, kindIndices.last()))
              kindExprs.add(PathUtils.unfold(monolithicExpr.propExpr, kindIndices.last()))
              kindIndices.add(kindIndices.last().add(monolithicExpr.transOffsetIndex))
            }
            val ind = And(kindExprs + unfoldedPropExpr(kindIndices.last()))
            extractModel(And(bmc, ind), indices + kindIndices)
          } else {

            True()
          }

        SafetyResult.safe(PredState.of(proof), BoundedStatistics(iteration))
      } else null
    }
  }

  private fun itp(): SafetyResult<PredState, Trace<S, A>>? {
    val itpSolver = this.itpSolver!!
    logger.write(Logger.Level.MAINSTEP, "\tStarting IMC\n")

    itpSolver.push()

    val a = itpSolver.createMarker()
    val b = itpSolver.createMarker()
    val pattern = itpSolver.createBinPattern(a, b)

    if (iteration == 1) {
      WithPushPop(itpSolver).use {
        itpSolver.add(a, unfoldedInitExpr)
        itpSolver.add(a, Not(unfoldedPropExpr(indices.first())))

        if (itpSolver.check().isSat) {
          val trace = getTrace(itpSolver.model)
          logger.write(
            Logger.Level.MAINSTEP,
            "CeX found in the initial state (length ${trace.length()})\n",
          )
          return SafetyResult.unsafe(trace, PredState.of(), BoundedStatistics(iteration))
        }
      }
    }

    itpSolver.push()

    itpSolver.add(a, unfoldedInitExpr)
    itpSolver.add(a, exprs[0])
    itpSolver.add(b, exprs.subList(1, exprs.size))

    if (lfPathOnly()) { // indices contains currIndex as last()
      itpSolver.push()
      val loopfree = LinkedList<Expr<BoolType>>()
      for (indexing in indices) {
        if (indexing != indices.last()) {
          val allVarsSame =
            And(
              vars.map {
                Eq(PathUtils.unfold(it.ref, indexing), PathUtils.unfold(it.ref, indices.last()))
              }
            )
          loopfree.add(Not(allVarsSame))
        }
      }
      itpSolver.add(a, loopfree)

      if (itpSolver.check().isUnsat) {
        itpSolver.pop()
        itpSolver.pop()
        logger.write(Logger.Level.MAINSTEP, "Safety proven in IMC/BMC step\n")
        val proof =
          if (needProof) {
            // we enumerate all states explored by previous iteration of BMC
            val expr =
              SmartBoolExprs.And(
                exprs.subList(0, exprs.size - 1) +
                  //                  loopfree.subList(0, loopfree.size - 1) +
                  unfoldedInitExpr
              )
            extractModel(expr, indices.subList(0, indices.size - 1))
          } else {
            True()
          }
        return SafetyResult.safe(PredState.of(proof), BoundedStatistics(iteration))
      }
      itpSolver.pop()
    }

    itpSolver.add(b, Not(unfoldedPropExpr(indices.last())))

    val status = itpSolver.check()

    if (status.isSat) {
      val trace = getTrace(itpSolver.model)
      logger.write(Logger.Level.MAINSTEP, "CeX found in IMC/BMC step (length ${trace.length()})\n")
      itpSolver.pop()
      itpSolver.pop()
      return SafetyResult.unsafe(trace, PredState.of(), BoundedStatistics(iteration))
    }

    var img = unfoldedInitExpr
    while (itpSolver.check().isUnsat) {
      val interpolant = itpSolver.getInterpolant(pattern)
      val itpFormula =
        PathUtils.unfold(PathUtils.foldin(interpolant.eval(a), indices[1]), indices[0])
      itpSolver.pop()

      itpSolver.push()
      itpSolver.add(a, itpFormula)
      itpSolver.add(a, Not(img))
      val itpStatus = itpSolver.check()
      if (itpStatus.isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in IMC step\n")
        itpSolver.pop()
        itpSolver.pop()
        return SafetyResult.safe(
          PredState.of(extractModel(img, indices.subList(0, 1))),
          BoundedStatistics(iteration),
        )
      }
      itpSolver.pop()
      img = Or(img, itpFormula)

      itpSolver.push()
      itpSolver.add(a, itpFormula)
      itpSolver.add(a, exprs[0])
      itpSolver.add(b, exprs.subList(1, exprs.size))
      itpSolver.add(b, Not(unfoldedPropExpr(indices.last())))
    }

    itpSolver.pop()
    itpSolver.pop()
    return null
  }

  private fun getTrace(model: Valuation): Trace<S, A> {
    val stateList = LinkedList<S>()
    val actionList = LinkedList<A>()
    var lastValuation: Valuation? = null
    for (i in indices) {
      val valuation = PathUtils.extractValuation(model, i, vars)
      stateList.add(valToState(valuation))
      if (lastValuation != null) {
        actionList.add(biValToAction(lastValuation, valuation))
      }
      lastValuation = valuation
    }
    return if (reverseTrace) {
      Trace.of(
        stateList.reversed(),
        actionList.reversed().map { if (it is ReversibleAction) it.reverse(it) else it },
      )
    } else {
      Trace.of(stateList, actionList)
    }
  }

  private fun extractModel(
    expr: Expr<BoolType>,
    indices: List<VarIndexing> = this.indices,
  ): Expr<BoolType> {
    val consts = ExprUtils.getIndexedConstants(expr)
    val map = consts.associateWith { Var(it.name, it.type) }
    val variants =
      Or(
        indices.map {
          And(
            consts
              .filter { f -> it.get(f.varDecl) == f.index }
              .map { Eq(it.varDecl.ref, map[it]!!.ref) }
          )
        }
      )
    return And(ExprUtils.changeDecls(expr, map), variants)
  }
}
