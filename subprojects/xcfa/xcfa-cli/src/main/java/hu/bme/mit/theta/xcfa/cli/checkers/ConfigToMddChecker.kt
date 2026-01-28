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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.ReverseMEPass
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.MddProof
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.createFwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaPipelineChecker
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.params.MddConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

fun getMddChecker(
  xcfa: XCFA,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec> {
  val mddConfig = config.backendConfig.specConfig as MddConfig

  val refinementSolverFactory: SolverFactory = getSolver(mddConfig.solver, mddConfig.validateSolver)

  val solverPool = SolverPool(refinementSolverFactory)

  val baseChecker = { monolithicExpr: MonolithicExpr ->
    MddChecker(
      monolithicExpr,
      solverPool,
      logger,
      iterationStrategy = mddConfig.iterationStrategy,
      mddToExprStrategy = mddConfig.mddToExprStrategy
    )
  }
  val passes = mutableListOf<MonolithicExprPass<MddProof>>()

  if (mddConfig.cegar) {
    passes.add(PredicateAbstractionMEPass(createFwBinItpCheckerFactory(refinementSolverFactory)))
  }
  if (mddConfig.reversed) {
    passes.add(ReverseMEPass())
  }

  return XcfaPipelineChecker(
    xcfa,
    config.inputConfig.property,
    parseContext,
    baseChecker,
    passes,
    logger,
    config.outputConfig.acceptUnreliableSafe,
    true,
  )
}
