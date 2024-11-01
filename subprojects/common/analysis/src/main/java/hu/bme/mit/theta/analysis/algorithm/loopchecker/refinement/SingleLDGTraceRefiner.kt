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

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult
import hu.bme.mit.theta.analysis.algorithm.loopchecker.LDGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDG
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.SolverFactory

class SingleLDGTraceRefiner<S : ExprState, A : ExprAction, P : Prec>(
  private val strategy: LDGTraceCheckerStrategy,
  private val solverFactory: SolverFactory,
  private val refiner: JoiningPrecRefiner<S, A, P, ItpRefutation>,
  private val logger: Logger,
  private val init: Expr<BoolType> = True(),
) : LDGTraceRefiner<S, A, P> {

  override fun refine(witness: LDG<S, A>, prec: P): RefinerResult<P, LDGTrace<S, A>> {
    val ldgTraces = witness.traces
    check(ldgTraces.isNotEmpty()) { "${this.javaClass.simpleName} needs at least one trace!" }
    val ldgTrace = ldgTraces[0]
    val refutation: ExprTraceStatus<ItpRefutation> =
      strategy.check(ldgTrace, solverFactory, init, logger)
    if (refutation.isInfeasible) {
      val refinedPrecision: P =
        refiner.refine(prec, ldgTrace.toTrace(), refutation.asInfeasible().refutation)
      witness.pruneAll()
      return RefinerResult.spurious(refinedPrecision)
    }
    return RefinerResult.unsafe(ldgTrace)
  }
}
