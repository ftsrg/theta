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

import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.FULL
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.LAZY
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.RESULT
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection.ERROR_LOCATION
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.analysis.oc.AutoConflictFinderConfig.SIMPLE
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Backend.CEGAR
import hu.bme.mit.theta.xcfa.cli.params.Backend.OC
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions.CHECK
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.COI
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.NO_COI
import hu.bme.mit.theta.xcfa.cli.params.Domain.EXPL
import hu.bme.mit.theta.xcfa.cli.params.Domain.PRED_CART
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes.SERVER_ERROR
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes.SOLVER_ERROR
import hu.bme.mit.theta.xcfa.cli.params.ExprSplitterOptions.WHOLE
import hu.bme.mit.theta.xcfa.cli.params.InitPrec.EMPTY
import hu.bme.mit.theta.xcfa.cli.params.POR.AASPOR
import hu.bme.mit.theta.xcfa.cli.params.POR.SPOR
import hu.bme.mit.theta.xcfa.cli.params.Refinement.NWT_IT_WP
import hu.bme.mit.theta.xcfa.cli.params.Refinement.SEQ_ITP
import hu.bme.mit.theta.xcfa.cli.params.Search.*
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.model.XCFA
import java.nio.file.Paths

@Suppress("LocalVariableName")
fun complexPortfolio26(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {

  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseConfig =
    XcfaConfig<CFrontendConfig, CegarConfig>(
      inputConfig =
        InputConfig(
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          property = portfolioConfig.inputConfig.property,
        ),
      backendConfig =
        BackendConfig(
          backend = CEGAR,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig =
            CegarConfig(
              initPrec = EMPTY,
              cexMonitor = CHECK,
              abstractorConfig =
                CegarAbstractorConfig(
                  abstractionSolver = "Z3",
                  validateAbstractionSolver = false,
                  domain = EXPL,
                  maxEnum = 1,
                  search = ERR,
                ),
              refinerConfig =
                CegarRefinerConfig(
                  refinementSolver = "Z3",
                  validateRefinementSolver = false,
                  refinement = SEQ_ITP,
                  exprSplitter = WHOLE,
                  pruneStrategy = FULL,
                ),
            ),
        ),
      outputConfig =
        OutputConfig(
          resultFolder = Paths.get("./").toFile(), // cwd
          cOutputConfig = COutputConfig(disable = true),
          witnessConfig =
            WitnessConfig(
              disable = false,
              concretizerSolver = "Z3",
              validateConcretizerSolver = false,
              inputFileForWitness =
                portfolioConfig.outputConfig.witnessConfig.inputFileForWitness
                  ?: portfolioConfig.inputConfig.input,
            ),
          argConfig = ArgConfig(disable = true),
          enableOutput = portfolioConfig.outputConfig.enableOutput,
          acceptUnreliableSafe = portfolioConfig.outputConfig.acceptUnreliableSafe,
          xcfaOutputConfig = XcfaOutputConfig(disable = true),
          chcOutputConfig = ChcOutputConfig(disable = true),
        ),
      debugConfig = portfolioConfig.debugConfig,
    )

  if (parseContext.multiThreading) {
    val baseCegarConfig = baseConfig.backendConfig.specConfig!!
    val multiThreadedCegarConfig =
      baseCegarConfig.copy(
        coi = if (baseConfig.inputConfig.property == DATA_RACE) NO_COI else COI,
        porLevel = if (baseConfig.inputConfig.property == DATA_RACE) SPOR else AASPOR,
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = DFS),
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
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = BFS),
        refinerConfig = baseCegarConfig.refinerConfig.copy(pruneStrategy = LAZY),
      )
    baseConfig =
      baseConfig.copy(backendConfig = baseConfig.backendConfig.copy(specConfig = recursiveConfig))
  }

  val timeoutOrNotSolvableError =
    ExceptionTrigger(
      fallthroughExceptions =
        setOf(ErrorCodeException(SOLVER_ERROR.code), ErrorCodeException(SERVER_ERROR.code)),
      label = "TimeoutOrNotSolvableError",
    )
  val timeoutOrSolverError =
    ExceptionTrigger(
      fallthroughExceptions = setOf(ErrorCodeException(SERVER_ERROR.code)),
      label = "TimeoutOrSolverError",
    )
  val solverError = ExceptionTrigger(ErrorCodeException(SOLVER_ERROR.code), label = "SolverError")
  val anyError = ExceptionTrigger(label = "Anything")

  fun getStm(trait: MainTrait, inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    return when (trait) {
      BITWISE -> {
        val config_BITWISE_EXPL_NWT_IT_WP_cvc5 =
          ConfigNode(
            "BITWISE_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = NWT_IT_WP,
              timeoutMs = 100000,
            ),
            checker,
          )
        val config_BITWISE_EXPL_NWT_IT_WP_Z3 =
          ConfigNode(
            "BITWISE_EXPL_NWT_IT_WP_Z3-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = NWT_IT_WP,
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
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = NWT_IT_WP,
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
              domain = PRED_CART,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = SEQ_ITP,
              timeoutMs = 0,
            ),
            checker,
          )
        edges.add(
          Edge(config_BITWISE_EXPL_SEQ_ITP_mathsat, config_BITWISE_EXPL_SEQ_ITP_cvc5, solverError)
        )

        STM(config_BITWISE_EXPL_NWT_IT_WP_cvc5, edges)
      }

      FLOAT -> {
        val config_FLOAT_EXPL_NWT_IT_WP_cvc5 =
          ConfigNode(
            "FLOAT_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = NWT_IT_WP,
              timeoutMs = 200000,
            ),
            checker,
          )
        val config_FLOAT_EXPL_NWT_IT_WP_Z3 =
          ConfigNode(
            "FLOAT_EXPL_NWT_IT_WP_Z3-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = NWT_IT_WP,
              timeoutMs = 200000,
            ),
            checker,
          )
        edges.add(
          Edge(config_FLOAT_EXPL_NWT_IT_WP_cvc5, config_FLOAT_EXPL_NWT_IT_WP_Z3, solverError)
        )
        val config_FLOAT_EXPL_NWT_IT_WP_mathsat =
          ConfigNode(
            "FLOAT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              validateRefinementSolver = true,
              refinement = NWT_IT_WP,
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
              domain = PRED_CART,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              validateRefinementSolver = true,
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = SEQ_ITP,
              timeoutMs = 0,
            ),
            checker,
          )
        edges.add(
          Edge(
            config_FLOAT_PRED_CART_SEQ_ITP_mathsat,
            config_FLOAT_PRED_CART_SEQ_ITP_cvc5,
            solverError,
          )
        )
        val config_FLOAT_EXPL_SEQ_ITP_mathsat =
          ConfigNode(
            "FLOAT_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              validateRefinementSolver = true,
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = SEQ_ITP,
              timeoutMs = 0,
            ),
            checker,
          )
        edges.add(
          Edge(config_FLOAT_EXPL_SEQ_ITP_mathsat, config_FLOAT_EXPL_SEQ_ITP_cvc5, solverError)
        )

        STM(config_FLOAT_EXPL_NWT_IT_WP_cvc5, edges)
      }

      LIN_INT -> {
        val config_LIN_INT_EXPL_NWT_IT_WP_mathsat =
          ConfigNode(
            "LIN_INT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = NWT_IT_WP,
              timeoutMs = 100000,
            ),
            checker,
          )
        val config_LIN_INT_EXPL_NWT_IT_WP_Z3 =
          ConfigNode(
            "LIN_INT_EXPL_NWT_IT_WP_Z3-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = NWT_IT_WP,
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
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "z3:4.12.2",
              refinementSolver = "z3:4.12.2",
              refinement = SEQ_ITP,
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

        STM(config_LIN_INT_EXPL_NWT_IT_WP_mathsat, edges)
      }

      NONLIN_INT -> {
        val config_NONLIN_INT_EXPL_NWT_IT_WP_Z3 =
          ConfigNode(
            "NONLIN_INT_EXPL_NWT_IT_WP_Z3-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = NWT_IT_WP,
              timeoutMs = 100000,
            ),
            checker,
          )
        val config_NONLIN_INT_EXPL_NWT_IT_WP_mathsat =
          ConfigNode(
            "NONLIN_INT_EXPL_NWT_IT_WP_mathsat:5.6.10-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = NWT_IT_WP,
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
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "z3:4.12.2",
              refinementSolver = "z3:4.12.2",
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
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
              domain = EXPL,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = NWT_IT_WP,
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

        STM(config_NONLIN_INT_EXPL_NWT_IT_WP_Z3, edges)
      }

      ARR -> {
        val config_ARR_EXPL_NWT_IT_WP_cvc5 =
          ConfigNode(
            "ARR_EXPL_NWT_IT_WP_cvc5:1.0.8-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = NWT_IT_WP,
              timeoutMs = 100000,
            ),
            checker,
          )
        val config_ARR_EXPL_NWT_IT_WP_Z3 =
          ConfigNode(
            "ARR_EXPL_NWT_IT_WP_Z3-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = NWT_IT_WP,
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
              domain = PRED_CART,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "z3:4.12.2",
              refinementSolver = "z3:4.12.2",
              refinement = SEQ_ITP,
              timeoutMs = 300000,
            ),
            checker,
          )
        edges.add(
          Edge(config_ARR_PRED_CART_SEQ_ITP_Z3, config_ARR_PRED_CART_SEQ_ITP_z3, solverError)
        )
        val config_ARR_PRED_CART_SEQ_ITP_princess =
          ConfigNode(
            "ARR_PRED_CART_SEQ_ITP_princess:2023-06-19-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = PRED_CART,
              abstractionSolver = "princess:2023-06-19",
              refinementSolver = "princess:2023-06-19",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "cvc5:1.0.8",
              refinementSolver = "cvc5:1.0.8",
              refinement = SEQ_ITP,
              timeoutMs = 500000,
            ),
            checker,
          )
        edges.add(
          Edge(
            config_ARR_PRED_CART_SEQ_ITP_princess,
            config_ARR_PRED_CART_SEQ_ITP_cvc5,
            solverError,
          )
        )

        STM(config_ARR_EXPL_NWT_IT_WP_cvc5, edges)
      }

      MULTITHREAD -> {
        val config_MULTITHREAD_EXPL_SEQ_ITP_Z3 =
          ConfigNode(
            "MULTITHREAD_EXPL_SEQ_ITP_Z3-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
              timeoutMs = 150000,
            ),
            checker,
          )
        val config_MULTITHREAD_EXPL_SEQ_ITP_mathsat =
          ConfigNode(
            "MULTITHREAD_EXPL_SEQ_ITP_mathsat:5.6.10-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
              timeoutMs = 150000,
            ),
            checker,
          )
        edges.add(
          Edge(
            config_MULTITHREAD_EXPL_SEQ_ITP_Z3,
            config_MULTITHREAD_EXPL_SEQ_ITP_mathsat,
            solverError,
          )
        )
        val config_MULTITHREAD_EXPL_NWT_IT_WP_z3 =
          ConfigNode(
            "MULTITHREAD_EXPL_NWT_IT_WP_z3:4.12.2-$inProcess",
            baseConfig.adaptConfig(
              inProcess = inProcess,
              domain = EXPL,
              abstractionSolver = "z3:4.12.2",
              refinementSolver = "z3:4.12.2",
              refinement = NWT_IT_WP,
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
              domain = EXPL,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = NWT_IT_WP,
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
              domain = PRED_CART,
              abstractionSolver = "Z3",
              refinementSolver = "Z3",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "mathsat:5.6.10",
              refinementSolver = "mathsat:5.6.10",
              refinement = SEQ_ITP,
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
              domain = PRED_CART,
              abstractionSolver = "z3:4.12.2",
              refinementSolver = "z3:4.12.2",
              refinement = SEQ_ITP,
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
        val cegarStm = STM(config_MULTITHREAD_EXPL_SEQ_ITP_Z3, edges)

        if (baseConfig.inputConfig.property == ERROR_LOCATION) {
          val config_OC =
            XcfaConfig<CFrontendConfig, OcConfig>(
              inputConfig = baseConfig.inputConfig,
              backendConfig =
                BackendConfig(
                  backend = OC,
                  solverHome = baseConfig.backendConfig.solverHome,
                  timeoutMs = 500_000,
                  inProcess = inProcess,
                  specConfig = OcConfig(autoConflict = SIMPLE),
                ),
              outputConfig = baseConfig.outputConfig,
              debugConfig = baseConfig.debugConfig,
            )
          val oc = ConfigNode("MULTITHREAD_OC-$inProcess", config_OC, checker)
          val cegar = HierarchicalNode("MULTITHREAD_CEGAR-$inProcess", cegarStm)
          val exitOcEdge = Edge(oc, cegar, anyError)
          STM(oc, setOf(exitOcEdge))
        } else {
          cegarStm
        }
      }

      PTR -> {
        val config_EXPL =
          ConfigNode(
            "PTR_EXPL-$inProcess",
            baseConfig.adaptConfig(inProcess = inProcess, domain = EXPL, timeoutMs = 100_000),
            checker,
          )
        val config_PRED_CART =
          ConfigNode(
            "PTR_PRED_CART-$inProcess",
            baseConfig.adaptConfig(inProcess = inProcess, domain = PRED_CART),
            checker,
          )
        edges.add(
          Edge(
            config_EXPL,
            config_PRED_CART,
            if (inProcess) timeoutOrNotSolvableError else anyError,
          )
        )
        STM(config_EXPL, edges)
      }
    }
  }

  val mainTrait =
    when {
      parseContext.multiThreading -> MULTITHREAD
      xcfa.procedures.any { p -> p.edges.any { it.label.dereferences.isNotEmpty() } } -> PTR
      ArithmeticTrait.FLOAT in parseContext.arithmeticTraits -> FLOAT
      ArithmeticTrait.ARR in parseContext.arithmeticTraits -> ARR
      ArithmeticTrait.BITWISE in parseContext.arithmeticTraits -> BITWISE
      ArithmeticTrait.NONLIN_INT in parseContext.arithmeticTraits -> NONLIN_INT
      else -> LIN_INT
    }

  logger.write(RESULT, "Using portfolio $mainTrait\n")

  if (portfolioConfig.debugConfig.debug) {
    return getStm(mainTrait, false)
  }

  val inProcessStm = getStm(mainTrait, true)
  val notInProcessStm = getStm(mainTrait, false)
  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)
  val fallbackEdge = Edge(inProcess, notInProcess, anyError)

  return STM(inProcess, setOf(fallbackEdge))
}
