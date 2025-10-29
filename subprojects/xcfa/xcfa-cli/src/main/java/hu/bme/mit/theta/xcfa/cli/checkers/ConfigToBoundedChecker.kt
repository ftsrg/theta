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
import hu.bme.mit.theta.analysis.algorithm.bounded.BoundedChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MEPipelineCheckerConstructorArguments
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.MonolithicExprPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.FormalismPipelineChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.L2SMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.PredicateAbstractionMEPass
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.passes.ReverseMEPass
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.createFwBinItpCheckerFactory
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.XcfaToMonolithicAdapter
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.model.XCFA

fun getBoundedChecker(
  xcfa: XCFA,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec> {

  val boundedConfig = config.backendConfig.specConfig as BoundedConfig

  val baseChecker = { monolithicExpr: MonolithicExpr ->
    BoundedChecker(
      monolithicExpr = monolithicExpr,
      bmcSolver =
        tryGetSolver(boundedConfig.bmcConfig.bmcSolver, boundedConfig.bmcConfig.validateBMCSolver)
          ?.createSolver(),
      bmcEnabled = { !boundedConfig.bmcConfig.disable },
      lfPathOnly = { !boundedConfig.bmcConfig.nonLfPath },
      itpSolver =
        tryGetSolver(boundedConfig.itpConfig.itpSolver, boundedConfig.itpConfig.validateItpSolver)
          ?.createItpSolver(),
      imcEnabled = { !boundedConfig.itpConfig.disable },
      indSolver =
        tryGetSolver(boundedConfig.indConfig.indSolver, boundedConfig.indConfig.validateIndSolver)
          ?.createSolver(),
      kindEnabled = { !boundedConfig.indConfig.disable },
      logger = logger,
      needProof = true,
    )
  }

  val passes = mutableListOf<MonolithicExprPass<PredState>>()
  if (config.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION) {
    passes.add(L2SMEPass())
  }
  if (boundedConfig.cegar) {
    passes.add(
      PredicateAbstractionMEPass(
        createFwBinItpCheckerFactory(
          tryGetSolver(
            boundedConfig.bmcConfig.bmcSolver,
            boundedConfig.bmcConfig.validateBMCSolver,
          )!!
        )
      )
    )
  }
  if (boundedConfig.reversed) {
    passes.add(ReverseMEPass())
  }
  return FormalismPipelineChecker(
    model = parseContext,
    modelAdapter = XcfaToMonolithicAdapter(xcfa),
    MEPipelineCheckerConstructorArguments(baseChecker, passes, logger = logger),
  )
}

private fun tryGetSolver(name: String, validate: Boolean): SolverFactory? {
  return try {
    getSolver(name, validate)
  } catch (_: Throwable) {
    null
  }
}
