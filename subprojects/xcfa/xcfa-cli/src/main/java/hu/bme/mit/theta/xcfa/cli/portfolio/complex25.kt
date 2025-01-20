/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType.efficient
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait.*
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
import hu.bme.mit.theta.xcfa.cli.params.POR.*
import hu.bme.mit.theta.xcfa.cli.params.Refinement.NWT_IT_WP
import hu.bme.mit.theta.xcfa.cli.params.Refinement.SEQ_ITP
import hu.bme.mit.theta.xcfa.cli.params.Search.*
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass
import java.nio.file.Paths

fun complexPortfolio25(
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
          lbeLevel = LbePass.level,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = efficient),
        ),
      backendConfig =
        BackendConfig(
          backend = CEGAR,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig =
            CegarConfig(
              initPrec = EMPTY,
              porLevel = NOPOR,
              porRandomSeed = -1,
              coi = NO_COI,
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
          versionInfo = false,
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

  val ocConfig = { inProcess: Boolean ->
    XcfaConfig(
      inputConfig = baseConfig.inputConfig.copy(xcfaWCtx = Triple(xcfa, mcm, parseContext)),
      frontendConfig = baseConfig.frontendConfig,
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
  }

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

  if (xcfa.procedures.any { it.edges.any { it.label.dereferences.isNotEmpty() } }) {
    val inProcEdges = LinkedHashSet<Edge>()
    val notInProcEdges = LinkedHashSet<Edge>()
    val edges = LinkedHashSet<Edge>()

    val explTrue =
      ConfigNode(
        "PTR-expl-inproc",
        baseConfig.adaptConfig(inProcess = true, domain = EXPL, timeoutMs = 100_000),
        checker,
      )
    val predTrue =
      ConfigNode(
        "PTR-pred-inproc",
        baseConfig.adaptConfig(inProcess = true, domain = PRED_CART),
        checker,
      )
    inProcEdges.add(Edge(explTrue, predTrue, timeoutOrNotSolvableError))
    val inproc = HierarchicalNode("inProc", STM(explTrue, inProcEdges))

    val explFalse =
      ConfigNode(
        "PTR-expl-notinproc",
        baseConfig.adaptConfig(inProcess = false, domain = EXPL, timeoutMs = 100_000),
        checker,
      )
    val predFalse =
      ConfigNode(
        "PTR-pred-notinproc",
        baseConfig.adaptConfig(inProcess = false, domain = PRED_CART),
        checker,
      )
    notInProcEdges.add(Edge(explFalse, predFalse, anyError))
    val notinproc = HierarchicalNode("notInProc", STM(explFalse, notInProcEdges))

    edges.add(Edge(inproc, notinproc, anyError))
    return if (portfolioConfig.debugConfig.debug) notinproc.innerSTM else STM(inproc, edges)
  }

  fun getStm(trait: ArithmeticTrait, inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()
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
    edges.add(Edge(config_FLOAT_EXPL_NWT_IT_WP_cvc5, config_FLOAT_EXPL_NWT_IT_WP_Z3, solverError))
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
      Edge(config_FLOAT_PRED_CART_SEQ_ITP_mathsat, config_FLOAT_PRED_CART_SEQ_ITP_cvc5, solverError)
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
    edges.add(Edge(config_FLOAT_EXPL_SEQ_ITP_mathsat, config_FLOAT_EXPL_SEQ_ITP_cvc5, solverError))
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
    edges.add(Edge(config_ARR_PRED_CART_SEQ_ITP_Z3, config_ARR_PRED_CART_SEQ_ITP_z3, solverError))
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
      Edge(config_ARR_PRED_CART_SEQ_ITP_princess, config_ARR_PRED_CART_SEQ_ITP_cvc5, solverError)
    )
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
      Edge(config_MULTITHREAD_EXPL_SEQ_ITP_Z3, config_MULTITHREAD_EXPL_SEQ_ITP_mathsat, solverError)
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
      FLOAT in parseContext.arithmeticTraits -> FLOAT
      ARR in parseContext.arithmeticTraits -> ARR
      BITWISE in parseContext.arithmeticTraits -> BITWISE
      NONLIN_INT in parseContext.arithmeticTraits -> NONLIN_INT
      else -> LIN_INT
    }

  logger.write(RESULT, "Using portfolio $mainTrait\n")

  var inProcessStm = getStm(mainTrait, true)
  var notInProcessStm = getStm(mainTrait, false)

  if (parseContext.multiThreading && baseConfig.inputConfig.property == ERROR_LOCATION) {
    val inProcOc = ConfigNode("OC", ocConfig(true), checker)
    val notInProcOc = ConfigNode("OC", ocConfig(false), checker)
    val inProcessCegar = HierarchicalNode("InProcessCegar", inProcessStm)
    val notInProcessCegar = HierarchicalNode("NotInprocessCegar", notInProcessStm)
    val exitOcInProcessEdge = Edge(inProcOc, inProcessCegar, ExceptionTrigger(label = "Anything"))
    val exitOcNotInProcessEdge =
      Edge(notInProcOc, notInProcessCegar, ExceptionTrigger(label = "Anything"))
    inProcessStm = STM(inProcOc, setOf(exitOcInProcessEdge))
    notInProcessStm = STM(notInProcOc, setOf(exitOcNotInProcessEdge))
  }

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(mainTrait, false)
  else STM(inProcess, setOf(fallbackEdge))
}
