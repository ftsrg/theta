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
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.portfolio.*
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import java.nio.file.Paths

fun portfolio(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseConfig =
    XcfaConfig(
      inputConfig =
        InputConfig(
          input = null,
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        ),
      frontendConfig =
        FrontendConfig(
          lbeLevel = LbePass.LbeLevel.LBE_SEQ,
          loopUnroll = 50,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = ArchitectureConfig.ArithmeticType.efficient),
        ),
      backendConfig =
        BackendConfig(
          backend = Backend.CEGAR,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig =
            CegarConfig(
              initPrec = InitPrec.EMPTY,
              por = POR.NOPOR,
              porSeed = -1,
              coi = ConeOfInfluenceMode.NO_COI,
              cexMonitor = CexMonitorOptions.CHECK,
              abstractorConfig =
                CegarAbstractorConfig(
                  abstractionSolver = "Z3",
                  validateAbstractionSolver = false,
                  domain = Domain.EXPL,
                  maxEnum = 1,
                  search = Search.ERR,
                ),
              refinerConfig =
                CegarRefinerConfig(
                  refinementSolver = "Z3",
                  validateRefinementSolver = false,
                  refinement = Refinement.SEQ_ITP,
                  exprSplitter = ExprSplitterOptions.WHOLE,
                  pruneStrategy = PruneStrategy.FULL,
                ),
            ),
        ),
      outputConfig =
        OutputConfig(
          versionInfo = false,
          resultFolder = Paths.get("./").toFile(), // cwd
          cOutputConfig = COutputConfig(disable = true),
          witnessConfig =
            WitnessConfig(
              disable = false,
              concretizerSolver = "Z3",
              validateConcretizerSolver = false,
            ),
          argConfig = ArgConfig(disable = true),
        ),
      debugConfig = portfolioConfig.debugConfig,
    )

  if (parseContext.multiThreading) {
    val baseCegarConfig = baseConfig.backendConfig.specConfig!!
    val multiThreadedCegarConfig =
      baseCegarConfig.copy(
        coi =
          if (baseConfig.inputConfig.property.verifiedProperty == ErrorDetection.DATA_RACE)
            ConeOfInfluenceMode.NO_COI
          else ConeOfInfluenceMode.COI,
        por =
          if (baseConfig.inputConfig.property.verifiedProperty == ErrorDetection.DATA_RACE) POR.SPOR
          else POR.AASPOR,
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = Search.DFS),
      )
    baseConfig =
      baseConfig.copy(
        backendConfig = baseConfig.backendConfig.copy(specConfig = multiThreadedCegarConfig)
      )
  }

  if (!xcfa.isInlined) {
    val baseCegarConfig = baseConfig.backendConfig.specConfig!!
    val recursiveConfig =
      baseCegarConfig.copy(
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = Search.BFS),
        refinerConfig = baseCegarConfig.refinerConfig.copy(pruneStrategy = PruneStrategy.LAZY),
      )
    baseConfig =
      baseConfig.copy(backendConfig = baseConfig.backendConfig.copy(specConfig = recursiveConfig))
  }

  return STM(ConfigNode("BaseConfig", baseConfig, checker), setOf())
}

portfolio(xcfa, mcm, parseContext, portfolioConfig, logger, uniqueLogger)
