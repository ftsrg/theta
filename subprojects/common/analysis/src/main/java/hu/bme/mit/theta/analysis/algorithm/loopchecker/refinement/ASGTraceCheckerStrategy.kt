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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.exception.TraceCheckingFailedException
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus.Feasible
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.*

enum class ASGTraceCheckerStrategy {
  MILANO {

    override fun <S : ExprState, A : ExprAction> check(
      trace: ASGTrace<S, A>,
      solverFactory: SolverFactory,
      init: Expr<BoolType>,
      logger: Logger,
    ) = MilanoASGTraceCheckerStrategy(trace, solverFactory, init, logger).check()
  },
  BOUNDED_UNROLLING {

    override fun <S : ExprState, A : ExprAction> check(
      trace: ASGTrace<S, A>,
      solverFactory: SolverFactory,
      init: Expr<BoolType>,
      logger: Logger,
    ): ExprTraceStatus<ItpRefutation> {
      try {
        return BoundedUnrollingASGTraceCheckerStrategy(trace, solverFactory, init, 100, logger)
          .check()
      } catch (t: TraceCheckingFailedException) {
        logger.write(Logger.Level.INFO, "${t.message}\n")
        logger.write(Logger.Level.INFO, "Falling back to default strategy $default\n")
        return default.check(trace, solverFactory, init, logger)
      }
    }
  };

  companion object {

    val default = MILANO
  }

  abstract fun <S : ExprState, A : ExprAction> check(
    trace: ASGTrace<S, A>,
    solverFactory: SolverFactory,
    init: Expr<BoolType> = True(),
    logger: Logger = NullLogger.getInstance(),
  ): ExprTraceStatus<ItpRefutation>
}

abstract class AbstractASGTraceCheckerStrategy<S : ExprState, A : ExprAction>(
  private val trace: ASGTrace<S, A>,
  solverFactory: SolverFactory,
  private val init: Expr<BoolType>,
  private val logger: Logger,
) {
  protected val solver: ItpSolver = solverFactory.createItpSolver()
  protected val stateCount = trace.length() + 1
  protected val indexings = mutableListOf<VarIndexing>()
  protected val satMarker: ItpMarker = solver.createMarker()
  protected val unreachableMarker: ItpMarker = solver.createMarker()
  protected val pattern: ItpPattern = solver.createBinPattern(satMarker, unreachableMarker)
  protected val variables =
    trace.edges.flatMap {
      ExprUtils.getVars(it.source?.state?.toExpr() ?: True()) +
        ExprUtils.getVars(it.action?.toExpr() ?: True())
    }

  private fun findSatIndex(): Int {
    for (i in 1 until stateCount) {
      solver.push()
      indexings.add(indexings[i - 1].add(trace.getAction(i - 1)!!.nextIndexing()))
      solver.add(satMarker, PathUtils.unfold(trace.getState(i).toExpr(), indexings[i]))
      solver.add(satMarker, PathUtils.unfold(trace.getAction(i - 1)!!.toExpr(), indexings[i - 1]))
      if (solver.check().isUnsat) {
        solver.pop()
        return i - 1
      }
    }
    return stateCount - 1
  }

  abstract fun evaluateLoop(valuation: Valuation): ExprTraceStatus<ItpRefutation>

  fun check(): ExprTraceStatus<ItpRefutation> {
    solver.push()
    indexings.add(VarIndexingFactory.indexing(0))
    solver.add(satMarker, PathUtils.unfold(init, indexings[0]))
    solver.add(satMarker, PathUtils.unfold(trace.getState(0).toExpr(), indexings[0]))

    val satIndex = findSatIndex()
    if (satIndex < stateCount - 1) return infeasibleAsLoopIsUnreachable(satIndex)
    return evaluateLoop(solver.model)
  }

  private fun infeasibleAsLoopIsUnreachable(satPrefix: Int): ExprTraceStatus<ItpRefutation> {
    logger.write(Logger.Level.INFO, "Loop was unreachable%n")
    solver.add(
      unreachableMarker,
      PathUtils.unfold(trace.getState(satPrefix + 1).toExpr(), indexings[satPrefix + 1]),
    )
    solver.add(
      unreachableMarker,
      PathUtils.unfold(trace.getAction(satPrefix)!!.toExpr(), indexings[satPrefix]),
    )
    return infeasibleThroughInterpolant(satPrefix, indexings[satPrefix])
  }

  protected fun infeasibleThroughInterpolant(
    satPrefix: Int,
    indexing: VarIndexing,
  ): ExprTraceStatus<ItpRefutation> {
    solver.check()
    val interpolant: Interpolant = solver.getInterpolant(pattern)
    val interpolantExpr: Expr<BoolType> = interpolant.eval(satMarker)
    logInterpolant(interpolantExpr)
    try {
      val itpFolded: Expr<BoolType> = PathUtils.foldin(interpolantExpr, indexing)
      return ExprTraceStatus.infeasible(ItpRefutation.binary(itpFolded, satPrefix, stateCount))
    } catch (e: IllegalArgumentException) {
      logger.write(
        Logger.Level.INFO,
        "Interpolant expression: %s; indexing: %s%n",
        interpolantExpr,
        indexing,
      )
      throw e
    }
  }

  protected fun getItpRefutationFeasible(): Feasible<ItpRefutation> =
    ExprTraceStatus.feasible(
      Trace.of(
        indexings.map { PathUtils.extractValuation(solver.model, it) },
        (trace.tail + trace.loop).map { it.action },
      )
    )

  protected fun logInterpolant(expr: Expr<BoolType>) {
    logger.write(Logger.Level.INFO, "Interpolant : $expr%n")
  }
}
