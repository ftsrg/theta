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
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.L2SMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.ReverseMEPass
import hu.bme.mit.theta.analysis.algorithm.ic3.Ic3Checker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.createFwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaPipelineChecker
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.params.Ic3Config
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getIc3Checker(
  xcfa: XCFA,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec> {

  val ic3Config = config.backendConfig.specConfig as Ic3Config
  val solverFactory: SolverFactory = getSolver(ic3Config.solver, ic3Config.validateSolver)

  val baseChecker = { monolithicExpr: MonolithicExpr ->
    Ic3Checker(
      /* monolithicExpr = */ monolithicExpr,
      /* solverFactory = */ solverFactory,
      /* formerFramesOpt = */ true,
      /* unSatOpt = */ true,
      /* notBOpt = */ true,
      /* propagateOpt = */ true,
      /* filterOpt = */ true,
      /* propertyOpt = */ true,
      /* logger = */ logger,
    )
  }

  val passes = mutableListOf<MonolithicExprPass<EmptyProof>>()
  if (config.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION) {
    passes.add(L2SMEPass())
  }
  if (ic3Config.cegar) {
    passes.add(PredicateAbstractionMEPass(createFwBinItpCheckerFactory(solverFactory)))
  }
  if (ic3Config.reversed) {
    passes.add(ReverseMEPass())
  }

  return XcfaPipelineChecker(
    xcfa,
    config.inputConfig.property.verifiedProperty,
    parseContext,
    baseChecker,
    passes,
    logger,
  )
}
