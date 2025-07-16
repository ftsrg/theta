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
package hu.bme.mit.theta.xcfa.cli.portfolio

import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.UniqueWarningLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import java.nio.file.Paths

fun complexPortfolio23(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: UniqueWarningLogger,
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
          inProcess = false,
          specConfig =
            CegarConfig(
              initPrec = InitPrec.EMPTY,
              porLevel = POR.NOPOR,
              porRandomSeed = -1,
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
        coi = ConeOfInfluenceMode.COI,
        porLevel =
          if (baseConfig.inputConfig.property == ErrorDetection.DATA_RACE) POR.SPOR else POR.AASPOR,
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = Search.BFS),
        refinerConfig = baseCegarConfig.refinerConfig.copy(pruneStrategy = PruneStrategy.LAZY),
      )
    baseConfig =
      baseConfig.copy(
        backendConfig = baseConfig.backendConfig.copy(specConfig = multiThreadedCegarConfig)
      )
  }

  val timeoutTrigger =
    ExceptionTrigger(
      ErrorCodeException(ExitCodes.TIMEOUT.code),
      ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
      ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
      ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
      label = "Timeout",
    )

  val timeoutOrSolverError =
    ExceptionTrigger(
      ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
      ErrorCodeException(ExitCodes.TIMEOUT.code),
      ErrorCodeException(ExitCodes.VERIFICATION_STUCK.code),
      ErrorCodeException(ExitCodes.OUT_OF_MEMORY.code),
      ErrorCodeException(ExitCodes.GENERIC_ERROR.code),
      label = "TimeoutOrSolverError",
    )

  fun XcfaConfig<*, CegarConfig>.adaptConfig(
    initPrec: InitPrec = this.backendConfig.specConfig!!.initPrec,
    timeoutMs: Long = this.backendConfig.timeoutMs,
    domain: Domain = this.backendConfig.specConfig!!.abstractorConfig.domain,
    refinement: Refinement = this.backendConfig.specConfig!!.refinerConfig.refinement,
    abstractionSolver: String = this.backendConfig.specConfig!!.abstractorConfig.abstractionSolver,
    validateAbstractionSolver: Boolean =
      this.backendConfig.specConfig!!.abstractorConfig.validateAbstractionSolver,
    refinementSolver: String = this.backendConfig.specConfig!!.refinerConfig.refinementSolver,
    validateRefinementSolver: Boolean =
      this.backendConfig.specConfig!!.refinerConfig.validateRefinementSolver,
    inProcess: Boolean = this.backendConfig.inProcess,
  ): XcfaConfig<*, CegarConfig> {
    return copy(
      backendConfig =
        backendConfig.copy(
          timeoutMs = timeoutMs,
          inProcess = inProcess,
          specConfig =
            backendConfig.specConfig!!.copy(
              initPrec = initPrec,
              abstractorConfig =
                backendConfig.specConfig!!
                  .abstractorConfig
                  .copy(
                    abstractionSolver = abstractionSolver,
                    validateAbstractionSolver = validateAbstractionSolver,
                    domain = domain,
                  ),
              refinerConfig =
                backendConfig.specConfig!!
                  .refinerConfig
                  .copy(
                    refinementSolver = refinementSolver,
                    validateRefinementSolver = validateRefinementSolver,
                    refinement = refinement,
                  ),
            ),
        )
    )
  }

  val quickExplConfig = baseConfig.adaptConfig(initPrec = InitPrec.ALLVARS, timeoutMs = 90_000)
  val emptyExplConfig = baseConfig.adaptConfig(timeoutMs = 210_000)
  val predConfig =
    baseConfig.adaptConfig(domain = Domain.PRED_CART, refinement = Refinement.BW_BIN_ITP)

  fun integerStm(): STM {
    fun getStm(inProcess: Boolean): STM {
      val config_1_1 =
        ConfigNode(
          "QuickFullExpl_z3_4.10.1_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "z3:4.10.1",
            refinementSolver = "z3:4.10.1",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_2_1 =
        ConfigNode(
          "EmptyExpl_z3_4.10.1_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "z3:4.10.1",
            refinementSolver = "z3:4.10.1",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_3_1 =
        ConfigNode(
          "PredCart_z3_4.10.1_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "z3:4.10.1",
            refinementSolver = "z3:4.10.1",
          ),
          checker,
        )

      val config_1_2 =
        ConfigNode(
          "QuickFullExpl_Z3_$inProcess",
          quickExplConfig.adaptConfig(inProcess = inProcess),
          checker,
        )
      val config_2_2 =
        ConfigNode(
          "EmptyExpl_Z3_$inProcess",
          emptyExplConfig.adaptConfig(inProcess = inProcess),
          checker,
        )
      val config_3_2 =
        ConfigNode("PredCart_Z3_$inProcess", predConfig.adaptConfig(inProcess = inProcess), checker)

      val config_1_3 =
        ConfigNode(
          "QuickFullExpl_princess_2022_07_01_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "princess:2022-07-01",
            refinementSolver = "princess:2022-07-01",
          ),
          checker,
        )
      val config_2_3 =
        ConfigNode(
          "EmptyExpl_princess_2022_07_01_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "princess:2022-07-01",
            refinementSolver = "princess:2022-07-01",
          ),
          checker,
        )
      val config_3_3 =
        ConfigNode(
          "PredCart_mathsat_5.6.8_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
          ),
          checker,
        )

      val config_1_4 =
        ConfigNode(
          "QuickFullExpl_mathsat_5.6.8_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
          ),
          checker,
        )
      val config_2_4 =
        ConfigNode(
          "EmptyExpl_mathsat_5.6.8_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
          ),
          checker,
        )
      val config_3_4 =
        ConfigNode(
          "PredCart_princess_2022_07_01_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "princess:2022-07-01",
            refinementSolver = "princess:2022-07-01",
          ),
          checker,
        )

      val timeouts =
        setOf(
          Edge(config_1_1, config_2_1, timeoutTrigger),
          Edge(config_2_1, config_3_1, timeoutTrigger),
          Edge(config_1_2, config_2_2, timeoutTrigger),
          Edge(config_2_2, config_3_1, timeoutTrigger),
          Edge(config_1_3, config_2_3, timeoutTrigger),
          Edge(config_2_3, config_3_1, timeoutTrigger),
          Edge(
            config_1_4,
            config_2_4,
            if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything"),
          ),
          Edge(
            config_2_4,
            config_3_1,
            if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything"),
          ),
        )

      val notTimeout =
        if (inProcess)
          ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code), label = "SolverError")
        else
          ExceptionTrigger(
            fallthroughExceptions = timeoutTrigger.exceptions,
            label = "AnythingButTimeout",
          )

      val solverExceptions =
        setOf(
          Edge(config_1_1, config_1_2, notTimeout),
          Edge(config_1_2, config_1_3, notTimeout),
          Edge(config_1_3, config_1_4, notTimeout),
          Edge(config_2_1, config_2_2, notTimeout),
          Edge(config_2_2, config_2_3, notTimeout),
          Edge(config_2_3, config_2_4, notTimeout),
          Edge(config_3_1, config_3_2, notTimeout),
          Edge(config_3_2, config_3_3, notTimeout),
          Edge(config_3_3, config_3_4, notTimeout),
        )
      return STM(config_1_1, timeouts union solverExceptions)
    }

    val inProcess =
      HierarchicalNode(
        "InProcess",
        getStm(!portfolioConfig.debugConfig.debug),
      ) // if not debug, then in process, else not in process
    val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return STM(inProcess, setOf(fallbackEdge))
  }

  fun bitwiseStm(): STM {
    fun getStm(inProcess: Boolean): STM {
      val config_1_1 =
        ConfigNode(
          "QuickFullExpl_Z3_$inProcess",
          quickExplConfig.adaptConfig(inProcess = inProcess, refinement = Refinement.NWT_IT_WP),
          checker,
        )
      val config_2_1 =
        ConfigNode(
          "EmptyExpl_Z3_$inProcess",
          emptyExplConfig.adaptConfig(inProcess = inProcess, refinement = Refinement.NWT_IT_WP),
          checker,
        )
      val config_3_1 =
        ConfigNode(
          "PredCart_mathsat_5.6.8_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
          ),
          checker,
        )

      val config_1_2 =
        ConfigNode(
          "QuickFullExpl_cvc5_1.0.2_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_2_2 =
        ConfigNode(
          "EmptyExpl_cvc5_1.0.2_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_3_2 =
        ConfigNode(
          "PredCart_z3_4.10.1_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "z3:4.10.1",
            refinementSolver = "z3:4.10.1",
          ),
          checker,
        )

      val config_1_3 =
        ConfigNode(
          "QuickFullExpl_mathsat_5.6.8_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_2_3 =
        ConfigNode(
          "EmptyExpl_mathsat_5.6.8_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
            refinement = Refinement.SEQ_ITP,
          ),
          checker,
        )
      val config_3_3 =
        ConfigNode(
          "PredCart_cvc5_1.0.2_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )

      val timeouts =
        setOf(
          Edge(config_1_1, config_2_1, timeoutTrigger),
          Edge(config_2_1, config_3_1, timeoutTrigger),
          Edge(config_1_2, config_2_2, timeoutTrigger),
          Edge(config_2_2, config_3_1, timeoutTrigger),
          Edge(
            config_1_3,
            config_2_3,
            if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything"),
          ),
          Edge(
            config_2_3,
            config_3_1,
            if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything"),
          ),
        )

      val notTimeout =
        if (inProcess)
          ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code), label = "SolverError")
        else
          ExceptionTrigger(
            fallthroughExceptions = timeoutTrigger.exceptions,
            label = "AnythingButTimeout",
          )

      val solverExceptions =
        setOf(
          Edge(config_1_1, config_1_2, notTimeout),
          Edge(config_1_2, config_1_3, notTimeout),
          Edge(config_2_1, config_2_2, notTimeout),
          Edge(config_2_2, config_2_3, notTimeout),
          Edge(config_3_1, config_3_2, notTimeout),
          Edge(config_3_2, config_3_3, notTimeout),
        )
      return STM(config_1_1, timeouts union solverExceptions)
    }

    val inProcess =
      HierarchicalNode(
        "InProcess",
        getStm(!portfolioConfig.debugConfig.debug),
      ) // if not debug, then in process, else not in process
    val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return STM(inProcess, setOf(fallbackEdge))
  }

  fun floatsStm(): STM {
    fun getStm(inProcess: Boolean): STM {
      val config_1_1 =
        ConfigNode(
          "QuickFullExpl_cvc5_1.0.2_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_2_1 =
        ConfigNode(
          "EmptyExpl_cvc5_1.0.2_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_3_1 =
        ConfigNode(
          "PredCart_mathsat_5.6.8_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
          ),
          checker,
        )

      val config_1_2 =
        ConfigNode(
          "QuickFullExpl_cvc5_1.0.2_seq_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.SEQ_ITP,
          ),
          checker,
        )
      val config_2_2 =
        ConfigNode(
          "EmptyExpl_cvc5_1.0.2_seq_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.SEQ_ITP,
          ),
          checker,
        )
      val config_3_2 =
        ConfigNode(
          "PredCart_bitwuzla_latest_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "bitwuzla:latest",
            refinementSolver = "bitwuzla:latest",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )

      val config_1_3 =
        ConfigNode(
          "QuickFullExpl_mathsat_5.6.8_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_2_3 =
        ConfigNode(
          "EmptyExpl_mathsat_5.6.8_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:5.6.8",
            refinementSolver = "mathsat:5.6.8",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_3_3 =
        ConfigNode(
          "PredCart_cvc5_1.0.2_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "cvc5:1.0.2",
            refinementSolver = "cvc5:1.0.2",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )

      val config_1_4 =
        ConfigNode(
          "QuickFullExpl_mathsat_fp_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:fp",
            refinementSolver = "mathsat:fp",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
          ),
          checker,
        )
      val config_2_4 =
        ConfigNode(
          "EmptyExpl_mathsat_fp_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:fp",
            refinementSolver = "mathsat:fp",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
          ),
          checker,
        )
      val config_3_4 =
        ConfigNode(
          "PredCart_mathsat_fp_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "mathsat:fp",
            refinementSolver = "mathsat:fp",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
          ),
          checker,
        )

      val config_1_5 =
        ConfigNode(
          "QuickFullExpl_Z3_$inProcess",
          quickExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_2_5 =
        ConfigNode(
          "EmptyExpl_Z3_$inProcess",
          emptyExplConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            validateAbstractionSolver = true,
            validateRefinementSolver = true,
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )
      val config_3_5 =
        ConfigNode(
          "PredCart_Z3_$inProcess",
          predConfig.adaptConfig(
            inProcess = inProcess,
            abstractionSolver = "Z3",
            refinementSolver = "Z3",
            refinement = Refinement.NWT_IT_WP,
          ),
          checker,
        )

      val timeouts =
        setOf(
          Edge(config_1_1, config_2_1, timeoutTrigger),
          Edge(config_2_1, config_3_1, timeoutTrigger),
          Edge(config_1_2, config_2_2, timeoutTrigger),
          Edge(config_2_2, config_3_1, timeoutTrigger),
          Edge(config_1_3, config_2_3, timeoutTrigger),
          Edge(config_2_3, config_3_1, timeoutTrigger),
          Edge(config_1_4, config_2_4, timeoutTrigger),
          Edge(config_2_4, config_3_1, timeoutTrigger),
          Edge(
            config_1_5,
            config_2_5,
            if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything"),
          ),
          Edge(
            config_2_5,
            config_3_1,
            if (inProcess) timeoutOrSolverError else ExceptionTrigger(label = "Anything"),
          ),
        )

      val notTimeout =
        if (inProcess)
          ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code), label = "SolverError")
        else
          ExceptionTrigger(
            fallthroughExceptions = timeoutTrigger.exceptions,
            label = "AnythingButTimeout",
          )

      val solverExceptions =
        setOf(
          Edge(config_1_1, config_1_2, notTimeout),
          Edge(config_1_2, config_1_3, notTimeout),
          Edge(config_1_3, config_1_4, notTimeout),
          Edge(config_1_4, config_1_5, notTimeout),
          Edge(config_2_1, config_2_2, notTimeout),
          Edge(config_2_2, config_2_3, notTimeout),
          Edge(config_2_3, config_2_4, notTimeout),
          Edge(config_2_4, config_2_5, notTimeout),
          Edge(config_3_1, config_3_2, notTimeout),
          Edge(config_3_2, config_3_3, notTimeout),
          Edge(config_3_3, config_3_4, notTimeout),
          Edge(config_3_4, config_3_5, notTimeout),
        )
      return STM(config_1_1, timeouts union solverExceptions)
    }

    val inProcess =
      HierarchicalNode(
        "InProcess",
        getStm(!portfolioConfig.debugConfig.debug),
      ) // if not debug, then in process, else not in process
    val notInProcess = HierarchicalNode("NotInprocess", getStm(false))

    val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

    return STM(inProcess, setOf(fallbackEdge))
  }

  return if (parseContext.arithmeticTraits.contains(ArithmeticTrait.FLOAT)) floatsStm()
  else if (parseContext.arithmeticTraits.contains(ArithmeticTrait.BITWISE)) bitwiseStm()
  else integerStm()
}
