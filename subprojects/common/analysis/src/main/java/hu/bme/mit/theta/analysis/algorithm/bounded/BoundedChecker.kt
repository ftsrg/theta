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
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import java.util.*

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
  private val imcFpSolver: Solver? = null,
  private val imcEnabled: (Int) -> Boolean = { itpSolver != null && imcFpSolver != null },
  private val indSolver: Solver? = null,
  private val kindEnabled: (Int) -> Boolean = { indSolver != null },
  private val valToState: (Valuation) -> S,
  private val biValToAction: (Valuation, Valuation) -> A,
  private val logger: Logger,
) : SafetyChecker<EmptyProof, Trace<S, A>, UnitPrec> {

  private val vars = monolithicExpr.vars
  private val unfoldedInitExpr =
    PathUtils.unfold(monolithicExpr.initExpr, VarIndexingFactory.indexing(0))
  private val unfoldedPropExpr = { i: VarIndexing -> PathUtils.unfold(monolithicExpr.propExpr, i) }
  private val indices = mutableListOf(monolithicExpr.initOffsetIndex)
  private val exprs = mutableListOf<Expr<BoolType>>()
  private var kindLastIterLookup = 0
  private var iteration = 0

  init {
    check(bmcSolver != itpSolver || bmcSolver == null) { "Use distinct solvers for BMC and IMC!" }
    check(bmcSolver != indSolver || bmcSolver == null) { "Use distinct solvers for BMC and KInd!" }
    check(itpSolver != indSolver || itpSolver == null) { "Use distinct solvers for IMC and KInd!" }
    check((itpSolver == null) == (imcFpSolver == null)) {
      "Both itpSolver and imcFpSolver must be either null or non-null!"
    }
  }

  override fun check(prec: UnitPrec?): SafetyResult<EmptyProof, Trace<S, A>> {

    iteration = 0

    val isBmcEnabled = bmcEnabled() // we don't allow per-iteration setting of bmc enabledness
    bmcSolver?.add(unfoldedInitExpr)

    while (!shouldGiveUp(iteration)) {
      iteration++
      logger.write(Logger.Level.MAINSTEP, "Starting iteration $iteration\n")

      exprs.add(PathUtils.unfold(monolithicExpr.transExpr, indices.last()))

      indices.add(indices.last().add(monolithicExpr.transOffsetIndex))

      if (isBmcEnabled) {
        bmc()?.let {
          logger.write(Logger.Level.RESULT, "%s%n", it)
          return it
        }
      }

      if (kindEnabled(iteration)) {
        if (!isBmcEnabled) {
          error("Bad configuration: induction check should always be preceded by a BMC/SAT check")
        }
        kind()?.let {
          logger.write(Logger.Level.RESULT, "%s%n", it)
          return it
        }
        kindLastIterLookup = iteration
      }

      if (imcEnabled(iteration)) {
        itp()?.let {
          logger.write(Logger.Level.RESULT, "%s%n", it)
          return it
        }
      }
    }
    return SafetyResult.unknown(BoundedStatistics(iteration))
  }

  private fun bmc(): SafetyResult<EmptyProof, Trace<S, A>>? {
    val bmcSolver = this.bmcSolver!!
    logger.write(Logger.Level.MAINSTEP, "\tStarting BMC\n")

    bmcSolver.add(exprs.last())

    if (lfPathOnly()) { // indices contains currIndex as last()
      for (indexing in indices) {
        if (indexing != indices.last()) {
          val allVarsSame =
            And(
              vars.map {
                Eq(PathUtils.unfold(it.ref, indexing), PathUtils.unfold(it.ref, indices.last()))
              }
            )
          bmcSolver.add(Not(allVarsSame))
        }
      }

      if (bmcSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in BMC step\n")
        return SafetyResult.safe(EmptyProof.getInstance(), BoundedStatistics(iteration))
      }
    }

    return WithPushPop(bmcSolver).use {
      bmcSolver.add(Not(unfoldedPropExpr(indices.last())))

      if (bmcSolver.check().isSat) {
        val trace = getTrace(bmcSolver.model)
        logger.write(Logger.Level.MAINSTEP, "CeX found in BMC step (length ${trace.length()})\n")
        SafetyResult.unsafe(trace, EmptyProof.getInstance(), BoundedStatistics(iteration))
      } else null
    }
  }

  private fun kind(): SafetyResult<EmptyProof, Trace<S, A>>? {
    val indSolver = this.indSolver!!

    logger.write(Logger.Level.MAINSTEP, "\tStarting k-induction\n")

    exprs.subList(kindLastIterLookup, exprs.size).forEach { indSolver.add(it) }
    indices.subList(kindLastIterLookup, indices.size - 1).forEach {
      indSolver.add(unfoldedPropExpr(it))
    }

    return WithPushPop(indSolver).use {
      indSolver.add(Not(unfoldedPropExpr(indices.last())))

      if (indSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in k-induction step\n")
        SafetyResult.safe(EmptyProof.getInstance(), BoundedStatistics(iteration))
      } else null
    }
  }

  private fun itp(): SafetyResult<EmptyProof, Trace<S, A>>? {
    val itpSolver = this.itpSolver!!
    val imcFpSolver = this.imcFpSolver!!
    logger.write(Logger.Level.MAINSTEP, "\tStarting IMC\n")

    itpSolver.push()

    val a = itpSolver.createMarker()
    val b = itpSolver.createMarker()
    val pattern = itpSolver.createBinPattern(a, b)

    itpSolver.push()

    itpSolver.add(a, exprs[0])
    itpSolver.add(b, exprs.subList(1, exprs.size))

    itpSolver.push()

    itpSolver.add(a, unfoldedInitExpr)

    if (lfPathOnly()) { // indices contains currIndex as last()
      itpSolver.push()
      for (indexing in indices) {
        if (indexing != indices.last()) {
          val allVarsSame =
            And(
              vars.map {
                Eq(PathUtils.unfold(it.ref, indexing), PathUtils.unfold(it.ref, indices.last()))
              }
            )
          itpSolver.add(a, Not(allVarsSame))
        }
      }

      if (itpSolver.check().isUnsat) {
        itpSolver.popAll()
        logger.write(Logger.Level.MAINSTEP, "Safety proven in IMC/BMC step\n")
        return SafetyResult.safe(EmptyProof.getInstance(), BoundedStatistics(iteration))
      }
      itpSolver.pop()
    }

    itpSolver.pop()
    itpSolver.add(b, Not(unfoldedPropExpr(indices.last())))
    itpSolver.push()
    itpSolver.add(a, unfoldedInitExpr)

    if (itpSolver.check().isSat) {
      val trace = getTrace(itpSolver.model)
      logger.write(Logger.Level.MAINSTEP, "CeX found in IMC/BMC step (length ${trace.length()})\n")
      itpSolver.popAll()
      return SafetyResult.unsafe(trace, EmptyProof.getInstance(), BoundedStatistics(iteration))
    }

    var img = unfoldedInitExpr
    while (itpSolver.check().isUnsat) {
      val interpolant = itpSolver.getInterpolant(pattern)
      val itpFormula =
        PathUtils.unfold(PathUtils.foldin(interpolant.eval(a), indices[1]), indices[0])

      imcFpSolver.push()
      imcFpSolver.add(itpFormula)
      imcFpSolver.add(Not(img))
      if (imcFpSolver.check().isUnsat) {
        logger.write(Logger.Level.MAINSTEP, "Safety proven in IMC step\n")
        imcFpSolver.popAll()
        itpSolver.popAll()
        return SafetyResult.safe(EmptyProof.getInstance(), BoundedStatistics(iteration))
      }
      imcFpSolver.popAll()

      img = Or(img, itpFormula)

      itpSolver.pop()
      itpSolver.push()
      itpSolver.add(a, itpFormula)
    }

    itpSolver.popAll()
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
    return Trace.of(stateList, actionList)
  }
}
