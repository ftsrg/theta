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
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass
import java.nio.file.Paths

fun complexPortfolio24(
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
          lbeLevel = LbePass.defaultLevel,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
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
          enableOutput = portfolioConfig.outputConfig.enableOutput,
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

  val timeoutOrNotSolvableError =
    ExceptionTrigger(
      fallthroughExceptions =
        setOf(
          ErrorCodeException(ExitCodes.SOLVER_ERROR.code),
          ErrorCodeException(ExitCodes.SERVER_ERROR.code),
        ),
      label = "TimeoutOrNotSolvableError",
    )

  val timeoutOrSolverError =
    ExceptionTrigger(
      fallthroughExceptions = setOf(ErrorCodeException(ExitCodes.SERVER_ERROR.code)),
      label = "TimeoutOrSolverError",
    )

  val solverError =
    ExceptionTrigger(ErrorCodeException(ExitCodes.SOLVER_ERROR.code), label = "SolverError")

  val anyError = ExceptionTrigger(label = "Anything")

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

  fun getStm(trait: MainTrait, inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()
    val config_BITWISE_EXPL_NWT_IT_WP_cvc5 =
      ConfigNode(
        "BITWISE_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    val config_BITWISE_EXPL_NWT_IT_WP_Z3 =
      ConfigNode(
        "BITWISE_EXPL_NWT_IT_WP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(
      Edge(config_BITWISE_EXPL_NWT_IT_WP_cvc5, config_BITWISE_EXPL_NWT_IT_WP_Z3, solverError)
    )
    val config_BITWISE_EXPL_NWT_IT_WP_mathsat =
      ConfigNode(
        "BITWISE_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(
      Edge(config_BITWISE_EXPL_NWT_IT_WP_Z3, config_BITWISE_EXPL_NWT_IT_WP_mathsat, solverError)
    )
    val config_BITWISE_PRED_CART_SEQ_ITP_mathsat =
      ConfigNode(
        "BITWISE_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_BITWISE_EXPL_NWT_IT_WP_cvc5,
        config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_BITWISE_EXPL_NWT_IT_WP_Z3,
        config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_BITWISE_EXPL_NWT_IT_WP_mathsat,
        config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_BITWISE_PRED_CART_SEQ_ITP_cvc5 =
      ConfigNode(
        "BITWISE_PRED_CART_SEQ_ITP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
        config_BITWISE_PRED_CART_SEQ_ITP_cvc5,
        solverError,
      )
    )
    val config_BITWISE_EXPL_SEQ_ITP_mathsat =
      ConfigNode(
        "BITWISE_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_BITWISE_PRED_CART_SEQ_ITP_mathsat,
        config_BITWISE_EXPL_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_BITWISE_PRED_CART_SEQ_ITP_cvc5,
        config_BITWISE_EXPL_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_BITWISE_EXPL_SEQ_ITP_cvc5 =
      ConfigNode(
        "BITWISE_EXPL_SEQ_ITP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(config_BITWISE_EXPL_SEQ_ITP_mathsat, config_BITWISE_EXPL_SEQ_ITP_cvc5, solverError)
    )
    val config_FLOAT_EXPL_NWT_IT_WP_cvc5 =
      ConfigNode(
        "FLOAT_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 200000,
        ),
        checker,
      )
    val config_FLOAT_EXPL_NWT_IT_WP_Z3 =
      ConfigNode(
        "FLOAT_EXPL_NWT_IT_WP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 200000,
        ),
        checker,
      )
    edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_cvc5, config_FLOAT_EXPL_NWT_IT_WP_Z3, solverError))
    val config_FLOAT_EXPL_NWT_IT_WP_mathsat =
      ConfigNode(
        "FLOAT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          validateRefinementSolver = true,
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 200000,
        ),
        checker,
      )
    edges.add(
      Edge(config_FLOAT_EXPL_NWT_IT_WP_Z3, config_FLOAT_EXPL_NWT_IT_WP_mathsat, solverError)
    )
    val config_FLOAT_PRED_CART_SEQ_ITP_mathsat =
      ConfigNode(
        "FLOAT_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          validateRefinementSolver = true,
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_FLOAT_EXPL_NWT_IT_WP_cvc5,
        config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_FLOAT_EXPL_NWT_IT_WP_Z3,
        config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_FLOAT_EXPL_NWT_IT_WP_mathsat,
        config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_FLOAT_PRED_CART_SEQ_ITP_cvc5 =
      ConfigNode(
        "FLOAT_PRED_CART_SEQ_ITP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(config_FLOAT_PRED_CART_SEQ_ITP_mathsat, config_FLOAT_PRED_CART_SEQ_ITP_cvc5, solverError)
    )
    val config_FLOAT_EXPL_SEQ_ITP_mathsat =
      ConfigNode(
        "FLOAT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          validateRefinementSolver = true,
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
        config_FLOAT_EXPL_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_FLOAT_PRED_CART_SEQ_ITP_cvc5,
        config_FLOAT_EXPL_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_FLOAT_EXPL_SEQ_ITP_cvc5 =
      ConfigNode(
        "FLOAT_EXPL_SEQ_ITP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(Edge(config_FLOAT_EXPL_SEQ_ITP_mathsat, config_FLOAT_EXPL_SEQ_ITP_cvc5, solverError))
    val config_LIN_INT_EXPL_NWT_IT_WP_mathsat =
      ConfigNode(
        "LIN_INT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    val config_LIN_INT_EXPL_NWT_IT_WP_Z3 =
      ConfigNode(
        "LIN_INT_EXPL_NWT_IT_WP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(
      Edge(config_LIN_INT_EXPL_NWT_IT_WP_mathsat, config_LIN_INT_EXPL_NWT_IT_WP_Z3, solverError)
    )
    val config_LIN_INT_EXPL_SEQ_ITP_Z3 =
      ConfigNode(
        "LIN_INT_EXPL_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 300000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_LIN_INT_EXPL_NWT_IT_WP_mathsat,
        config_LIN_INT_EXPL_SEQ_ITP_Z3,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_LIN_INT_EXPL_NWT_IT_WP_Z3,
        config_LIN_INT_EXPL_SEQ_ITP_Z3,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_LIN_INT_EXPL_SEQ_ITP_mathsat =
      ConfigNode(
        "LIN_INT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 300000,
        ),
        checker,
      )
    edges.add(
      Edge(config_LIN_INT_EXPL_SEQ_ITP_Z3, config_LIN_INT_EXPL_SEQ_ITP_mathsat, solverError)
    )
    val config_LIN_INT_PRED_CART_SEQ_ITP_Z3 =
      ConfigNode(
        "LIN_INT_PRED_CART_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_LIN_INT_EXPL_SEQ_ITP_Z3,
        config_LIN_INT_PRED_CART_SEQ_ITP_Z3,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_LIN_INT_EXPL_SEQ_ITP_mathsat,
        config_LIN_INT_PRED_CART_SEQ_ITP_Z3,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_LIN_INT_PRED_CART_SEQ_ITP_mathsat =
      ConfigNode(
        "LIN_INT_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_LIN_INT_PRED_CART_SEQ_ITP_Z3,
        config_LIN_INT_PRED_CART_SEQ_ITP_mathsat,
        solverError,
      )
    )
    val config_LIN_INT_PRED_CART_SEQ_ITP_z3 =
      ConfigNode(
        "LIN_INT_PRED_CART_SEQ_ITP_z3:4.12.2-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "z3:4.12.2",
          refinementSolver = "z3:4.12.2",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_LIN_INT_PRED_CART_SEQ_ITP_mathsat,
        config_LIN_INT_PRED_CART_SEQ_ITP_z3,
        solverError,
      )
    )
    val config_NONLIN_INT_EXPL_NWT_IT_WP_Z3 =
      ConfigNode(
        "NONLIN_INT_EXPL_NWT_IT_WP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    val config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat =
      ConfigNode(
        "NONLIN_INT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_NONLIN_INT_EXPL_NWT_IT_WP_Z3,
        config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat,
        solverError,
      )
    )
    val config_NONLIN_INT_EXPL_SEQ_ITP_Z3 =
      ConfigNode(
        "NONLIN_INT_EXPL_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_NONLIN_INT_EXPL_NWT_IT_WP_Z3,
        config_NONLIN_INT_EXPL_SEQ_ITP_Z3,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat,
        config_NONLIN_INT_EXPL_SEQ_ITP_Z3,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_NONLIN_INT_EXPL_SEQ_ITP_z3 =
      ConfigNode(
        "NONLIN_INT_EXPL_SEQ_ITP_z3:4.12.2-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "z3:4.12.2",
          refinementSolver = "z3:4.12.2",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(
      Edge(config_NONLIN_INT_EXPL_SEQ_ITP_Z3, config_NONLIN_INT_EXPL_SEQ_ITP_z3, solverError)
    )
    val config_NONLIN_INT_EXPL_SEQ_ITP_mathsat =
      ConfigNode(
        "NONLIN_INT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 200000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_NONLIN_INT_EXPL_SEQ_ITP_Z3,
        config_NONLIN_INT_EXPL_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_NONLIN_INT_EXPL_SEQ_ITP_z3,
        config_NONLIN_INT_EXPL_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat =
      ConfigNode(
        "NONLIN_INT_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_NONLIN_INT_EXPL_SEQ_ITP_mathsat,
        config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_NONLIN_INT_PRED_CART_SEQ_ITP_Z3 =
      ConfigNode(
        "NONLIN_INT_PRED_CART_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat,
        config_NONLIN_INT_PRED_CART_SEQ_ITP_Z3,
        solverError,
      )
    )
    val config_NONLIN_INT_EXPL_NWT_IT_WP_cvc5 =
      ConfigNode(
        "NONLIN_INT_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_NONLIN_INT_PRED_CART_SEQ_ITP_mathsat,
        config_NONLIN_INT_EXPL_NWT_IT_WP_cvc5,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_NONLIN_INT_PRED_CART_SEQ_ITP_Z3,
        config_NONLIN_INT_EXPL_NWT_IT_WP_cvc5,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_ARR_EXPL_NWT_IT_WP_cvc5 =
      ConfigNode(
        "ARR_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    val config_ARR_EXPL_NWT_IT_WP_Z3 =
      ConfigNode(
        "ARR_EXPL_NWT_IT_WP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 100000,
        ),
        checker,
      )
    edges.add(Edge(config_ARR_EXPL_NWT_IT_WP_cvc5, config_ARR_EXPL_NWT_IT_WP_Z3, solverError))
    val config_ARR_PRED_CART_SEQ_ITP_Z3 =
      ConfigNode(
        "ARR_PRED_CART_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 300000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_ARR_EXPL_NWT_IT_WP_cvc5,
        config_ARR_PRED_CART_SEQ_ITP_Z3,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_ARR_EXPL_NWT_IT_WP_Z3,
        config_ARR_PRED_CART_SEQ_ITP_Z3,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_ARR_PRED_CART_SEQ_ITP_z3 =
      ConfigNode(
        "ARR_PRED_CART_SEQ_ITP_z3:4.12.2-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "z3:4.12.2",
          refinementSolver = "z3:4.12.2",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 300000,
        ),
        checker,
      )
    edges.add(Edge(config_ARR_PRED_CART_SEQ_ITP_Z3, config_ARR_PRED_CART_SEQ_ITP_z3, solverError))
    val config_ARR_PRED_CART_SEQ_ITP_princess =
      ConfigNode(
        "ARR_PRED_CART_SEQ_ITP_princess:2023-06-19-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "princess:2023-06-19",
          refinementSolver = "princess:2023-06-19",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 500000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_ARR_PRED_CART_SEQ_ITP_Z3,
        config_ARR_PRED_CART_SEQ_ITP_princess,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_ARR_PRED_CART_SEQ_ITP_z3,
        config_ARR_PRED_CART_SEQ_ITP_princess,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_ARR_PRED_CART_SEQ_ITP_cvc5 =
      ConfigNode(
        "ARR_PRED_CART_SEQ_ITP_cvc5:1.0.8-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "cvc5:1.0.8",
          refinementSolver = "cvc5:1.0.8",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 500000,
        ),
        checker,
      )
    edges.add(
      Edge(config_ARR_PRED_CART_SEQ_ITP_princess, config_ARR_PRED_CART_SEQ_ITP_cvc5, solverError)
    )
    val config_MULTITHREAD_EXPL_SEQ_ITP_Z3 =
      ConfigNode(
        "MULTITHREAD_EXPL_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 150000,
        ),
        checker,
      )
    val config_MULTITHREAD_EXPL_SEQ_ITP_mathsat =
      ConfigNode(
        "MULTITHREAD_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 150000,
        ),
        checker,
      )
    edges.add(
      Edge(config_MULTITHREAD_EXPL_SEQ_ITP_Z3, config_MULTITHREAD_EXPL_SEQ_ITP_mathsat, solverError)
    )
    val config_MULTITHREAD_EXPL_NWT_IT_WP_z3 =
      ConfigNode(
        "MULTITHREAD_EXPL_NWT_IT_WP_z3:4.12.2-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "z3:4.12.2",
          refinementSolver = "z3:4.12.2",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 300000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_MULTITHREAD_EXPL_SEQ_ITP_Z3,
        config_MULTITHREAD_EXPL_NWT_IT_WP_z3,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_MULTITHREAD_EXPL_SEQ_ITP_mathsat,
        config_MULTITHREAD_EXPL_NWT_IT_WP_z3,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_MULTITHREAD_EXPL_NWT_IT_WP_mathsat =
      ConfigNode(
        "MULTITHREAD_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.EXPL,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.NWT_IT_WP,
          timeoutMs = 300000,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_MULTITHREAD_EXPL_NWT_IT_WP_z3,
        config_MULTITHREAD_EXPL_NWT_IT_WP_mathsat,
        solverError,
      )
    )
    val config_MULTITHREAD_PRED_CART_SEQ_ITP_Z3 =
      ConfigNode(
        "MULTITHREAD_PRED_CART_SEQ_ITP_Z3-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "Z3",
          refinementSolver = "Z3",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_MULTITHREAD_EXPL_NWT_IT_WP_z3,
        config_MULTITHREAD_PRED_CART_SEQ_ITP_Z3,
        if (inProcess) timeoutOrNotSolvableError else anyError,
      )
    )
    edges.add(
      Edge(
        config_MULTITHREAD_EXPL_NWT_IT_WP_mathsat,
        config_MULTITHREAD_PRED_CART_SEQ_ITP_Z3,
        if (inProcess) timeoutOrSolverError else anyError,
      )
    )
    val config_MULTITHREAD_PRED_CART_SEQ_ITP_mathsat =
      ConfigNode(
        "MULTITHREAD_PRED_CART_SEQ_ITP_mathsat:5.6.10-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "mathsat:5.6.10",
          refinementSolver = "mathsat:5.6.10",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_MULTITHREAD_PRED_CART_SEQ_ITP_Z3,
        config_MULTITHREAD_PRED_CART_SEQ_ITP_mathsat,
        solverError,
      )
    )
    val config_MULTITHREAD_PRED_CART_SEQ_ITP_z3 =
      ConfigNode(
        "MULTITHREAD_PRED_CART_SEQ_ITP_z3:4.12.2-$inProcess",
        baseConfig.adaptConfig(
          inProcess = inProcess,
          domain = Domain.PRED_CART,
          abstractionSolver = "z3:4.12.2",
          refinementSolver = "z3:4.12.2",
          refinement = Refinement.SEQ_ITP,
          timeoutMs = 0,
        ),
        checker,
      )
    edges.add(
      Edge(
        config_MULTITHREAD_PRED_CART_SEQ_ITP_mathsat,
        config_MULTITHREAD_PRED_CART_SEQ_ITP_z3,
        solverError,
      )
    )
    if (trait == BITWISE) {
      return STM(config_BITWISE_EXPL_NWT_IT_WP_cvc5, edges)
    }

    if (trait == FLOAT) {
      return STM(config_FLOAT_EXPL_NWT_IT_WP_cvc5, edges)
    }

    if (trait == LIN_INT) {
      return STM(config_LIN_INT_EXPL_NWT_IT_WP_mathsat, edges)
    }

    if (trait == NONLIN_INT) {
      return STM(config_NONLIN_INT_EXPL_NWT_IT_WP_Z3, edges)
    }

    if (trait == ARR) {
      return STM(config_ARR_EXPL_NWT_IT_WP_cvc5, edges)
    }

    if (trait == MULTITHREAD) {
      return STM(config_MULTITHREAD_EXPL_SEQ_ITP_Z3, edges)
    }

    error("Unknown trait!")
  }

  val mainTrait =
    when {
      parseContext.multiThreading -> MULTITHREAD
      ArithmeticTrait.FLOAT in parseContext.arithmeticTraits -> FLOAT
      ArithmeticTrait.ARR in parseContext.arithmeticTraits -> ARR
      ArithmeticTrait.BITWISE in parseContext.arithmeticTraits -> BITWISE
      ArithmeticTrait.NONLIN_INT in parseContext.arithmeticTraits -> NONLIN_INT
      else -> LIN_INT
    }

  logger.write(Logger.Level.RESULT, "Using portfolio $mainTrait\n")

  val inProcess = HierarchicalNode("InProcess", getStm(mainTrait, true))
  val notInProcess = HierarchicalNode("NotInprocess", getStm(mainTrait, false))

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(mainTrait, false)
  else STM(inProcess, setOf(fallbackEdge))
}
