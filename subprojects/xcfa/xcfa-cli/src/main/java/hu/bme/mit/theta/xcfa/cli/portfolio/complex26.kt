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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.ARR
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.BITWISE
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.FLOAT
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.LIN_INT
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.MULTITHREAD
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.NONLIN_INT
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.PTR
import hu.bme.mit.theta.xcfa.cli.portfolio.MainTrait.TERMINATION
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.dereferences

fun complex26(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  var baseCegarConfig = baseCegarConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseBoundedConfig = baseBoundedConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseMddConfig = baseMddConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseIc3Config = baseIc3Config(xcfa, mcm, parseContext, portfolioConfig, false)

  fun getStm(mainTrait: MainTrait, inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    fun cegar(
      timeout: Long,
      solver: String,
      domain: Domain = Domain.PRED_CART,
      refinement: Refinement = Refinement.SEQ_ITP,
    ): ConfigNode {
      return ConfigNode(
        "${domain.name}-${refinement.name}-${solver}-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = domain,
          refinement = refinement,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
        ),
        checker,
      )
    }

    val bmc = { timeout: Long, solver: String ->
      ConfigNode(
        "BMC-${solver}-$inProcess",
        baseBoundedConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = false,
          itpEnabled = false,
          timeoutMs = timeout,
          bmcSolver = solver,
        ),
        checker,
      )
    }

    val kind = { timeout: Long, solver: String ->
      ConfigNode(
        "KIND-${solver}-$inProcess",
        baseBoundedConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = true,
          indEnabled = true,
          itpEnabled = false,
          timeoutMs = timeout,
          bmcSolver = solver,
          indSolver = solver,
        ),
        checker,
      )
    }

    val imc = { timeout: Long, solver: String ->
      ConfigNode(
        "IMC-${solver}-$inProcess",
        baseBoundedConfig.adaptConfig(
          inProcess = inProcess,
          bmcEnabled = false,
          indEnabled = false,
          itpEnabled = true,
          timeoutMs = timeout,
          itpSolver = solver,
        ),
        checker,
      )
    }

    val ic3 = { timeout: Long, solver: String ->
      ConfigNode(
        "IC3-${solver}-$inProcess",
        baseIc3Config.copy(
          backendConfig =
            baseIc3Config.backendConfig.copy(
              parseInProcess = true,
              timeoutMs = timeout,
              inProcess = inProcess,
              specConfig =
                baseIc3Config.backendConfig.specConfig!!.copy(solver = solver, reversed = true),
            )
        ),
        checker,
      )
    }

    val ic3Cegar = { timeout: Long, solver: String ->
      ConfigNode(
        "IC3-cegar-${solver}-$inProcess",
        baseIc3Config.copy(
          backendConfig =
            baseIc3Config.backendConfig.copy(
              parseInProcess = true,
              timeoutMs = timeout,
              inProcess = inProcess,
              specConfig =
                baseIc3Config.backendConfig.specConfig!!.copy(
                  solver = solver,
                  cegar = true,
                  reversed = true,
                ),
            )
        ),
        checker,
      )
    }

    val mdd = { timeout: Long, solver: String ->
      ConfigNode(
        "MDD-${solver}-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig = baseMddConfig.backendConfig.specConfig!!.copy(solver = solver),
            )
        ),
        checker,
      )
    }

    val mddCegar = { timeout: Long, solver: String ->
      ConfigNode(
        "MDD-cegar-${solver}-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig =
                baseMddConfig.backendConfig.specConfig!!.copy(cegar = true, solver = solver),
            )
        ),
        checker,
      )
    }

    val complex =
      ConfigNode(
        "Complex-$inProcess",
        XcfaConfig(
          inputConfig =
            portfolioConfig.inputConfig.copy(
              xcfaWCtx =
                if (portfolioConfig.backendConfig.parseInProcess) null
                else Triple(xcfa, mcm, parseContext),
              propertyFile = null,
              property = portfolioConfig.inputConfig.property,
            ),
          frontendConfig = portfolioConfig.frontendConfig,
          backendConfig =
            (portfolioConfig.backendConfig as BackendConfig<PortfolioConfig>).copy(
              specConfig = PortfolioConfig("COMPLEX")
            ),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
        ),
        checker,
      )

    val termination =
      ConfigNode(
        "Termination-$inProcess",
        XcfaConfig(
          inputConfig =
            portfolioConfig.inputConfig.copy(
              xcfaWCtx =
                if (portfolioConfig.backendConfig.parseInProcess) null
                else Triple(xcfa, mcm, parseContext),
              propertyFile = null,
              property = portfolioConfig.inputConfig.property,
            ),
          frontendConfig = portfolioConfig.frontendConfig,
          backendConfig =
            (portfolioConfig.backendConfig as BackendConfig<PortfolioConfig>).copy(
              specConfig = PortfolioConfig("TERMINATION")
            ),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
        ),
        checker,
      )

    val multithread =
      ConfigNode(
        "MultiThread-$inProcess",
        XcfaConfig(
          inputConfig =
            portfolioConfig.inputConfig.copy(
              xcfaWCtx =
                if (portfolioConfig.backendConfig.parseInProcess) null
                else Triple(xcfa, mcm, parseContext),
              propertyFile = null,
              property = portfolioConfig.inputConfig.property,
            ),
          frontendConfig = portfolioConfig.frontendConfig,
          backendConfig =
            (portfolioConfig.backendConfig as BackendConfig<PortfolioConfig>).copy(
              specConfig = PortfolioConfig("MULTITHREAD")
            ),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
        ),
        checker,
      )

    infix fun ConfigNode.then(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, if (inProcess) timeoutOrNotSolvableError else anyError))
      return node
    }

    infix fun ConfigNode.onSolverError(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, solverError))
      return node
    }

    val (startingConfig, endConfig) =
      if (xcfa.isInlined) {
        when (mainTrait) {
          BITWISE -> {

            val kind = kind(300_000, "Z3:new")
            val pred_bw = cegar(300_000, "Z3", Domain.PRED_CART, Refinement.BW_BIN_ITP)
            val expl = cegar(200_000, "Z3:new", Domain.EXPL, Refinement.NWT_IT_WP)
            val bmc = bmc(150_000, "Z3:new")

            val kindMS = kind(300_000, "mathsat:5.6.12")
            val pred_bwMS =
              cegar(300_000, "mathsat:5.6.12", Domain.PRED_CART, Refinement.BW_BIN_ITP)
            val explMS = cegar(200_000, "mathsat:5.6.12", Domain.EXPL, Refinement.NWT_IT_WP)
            val bmcMS = bmc(150_000, "mathsat:5.6.12")

            kind then pred_bw then expl then bmc

            kindMS onSolverError kind
            pred_bwMS onSolverError pred_bw
            explMS onSolverError expl

            kindMS then pred_bwMS then explMS then bmcMS

            kindMS to bmcMS
          }
          FLOAT -> {
            // CVC by default, Z3 as fallback

            val kind = kind(300_000, "Z3:new")
            val pred_bw = cegar(300_000, "Z3", Domain.PRED_CART, Refinement.BW_BIN_ITP)
            val expl = cegar(200_000, "Z3:new", Domain.EXPL, Refinement.NWT_IT_WP)
            val bmc = bmc(150_000, "Z3:new")

            val kindCVC = kind(300_000, "cvc5:1.2.0")
            val pred_bwCVC = cegar(300_000, "cvc5:1.2.0", Domain.PRED_CART, Refinement.BW_BIN_ITP)
            val explCVC = cegar(200_000, "cvc5:1.2.0", Domain.EXPL, Refinement.NWT_IT_WP)
            val bmcCVC = bmc(150_000, "cvc5:1.2.0")

            kind then pred_bw then expl then bmc

            kindCVC onSolverError kind
            pred_bwCVC onSolverError pred_bw
            explCVC onSolverError expl
            bmcCVC onSolverError bmc

            kindCVC then pred_bwCVC then explCVC then bmcCVC

            kindCVC to bmcCVC
          }
          PTR,
          ARR,
          NONLIN_INT,
          LIN_INT -> {
            val kind = kind(300_000, "Z3:new")
            val pred_bw = cegar(300_000, "Z3", Domain.PRED_CART, Refinement.BW_BIN_ITP)
            val expl = cegar(200_000, "Z3:new", Domain.EXPL, Refinement.NWT_IT_WP)
            val bmc = bmc(150_000, "Z3:new")

            val kindMS = kind(300_000, "mathsat:5.6.12")
            val pred_bwMS =
              cegar(300_000, "mathsat:5.6.12", Domain.PRED_CART, Refinement.BW_BIN_ITP)
            val explMS = cegar(200_000, "mathsat:5.6.12", Domain.EXPL, Refinement.NWT_IT_WP)
            val bmcMS = bmc(150_000, "mathsat:5.6.12")

            kind then pred_bw then expl then bmc

            kind onSolverError kindMS
            pred_bw onSolverError pred_bwMS
            expl onSolverError explMS

            kindMS then pred_bwMS then explMS then bmcMS

            kind to bmc
          }

          MULTITHREAD -> {
            multithread to multithread
          }
          TERMINATION -> {
            termination to termination
          }
        }
      } else {
        val pred_bw = cegar(300_000, "Z3", Domain.PRED_CART, Refinement.BW_BIN_ITP)
        val expl = cegar(300_000, "Z3:new", Domain.EXPL, Refinement.NWT_IT_WP)
        val pred_seq = cegar(150_000, "Z3", Domain.PRED_CART, Refinement.SEQ_ITP)
        val expl_seq = cegar(150_000, "Z3", Domain.EXPL, Refinement.SEQ_ITP)

        val pred_bwMS = cegar(300_000, "mathsat:5.6.12", Domain.PRED_CART, Refinement.BW_BIN_ITP)
        val explMS = cegar(200_000, "mathsat:5.6.12", Domain.EXPL, Refinement.NWT_IT_WP)
        val pred_seqMS = cegar(150_000, "mathsat:5.6.12", Domain.PRED_CART, Refinement.SEQ_ITP)
        val expl_seqMS = cegar(150_000, "mathsat:5.6.12", Domain.EXPL, Refinement.SEQ_ITP)

        pred_bw then expl then pred_seq then expl_seq

        pred_bw onSolverError pred_bwMS
        expl onSolverError explMS
        pred_seq onSolverError pred_seqMS
        expl_seq onSolverError expl_seqMS

        pred_bwMS then explMS then pred_seqMS then expl_seqMS

        pred_bw to expl_seq
      }

    endConfig then complex

    return STM(startingConfig, edges)
  }

  val mainTrait =
    when {
      portfolioConfig.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION ->
        MainTrait.TERMINATION
      parseContext.multiThreading -> MULTITHREAD
      xcfa.procedures.any { p -> p.edges.any { it.label.dereferences.isNotEmpty() } } -> PTR
      ArithmeticTrait.FLOAT in parseContext.arithmeticTraits -> FLOAT
      ArithmeticTrait.ARR in parseContext.arithmeticTraits -> ARR
      ArithmeticTrait.BITWISE in parseContext.arithmeticTraits -> BITWISE
      ArithmeticTrait.NONLIN_INT in parseContext.arithmeticTraits -> NONLIN_INT
      else -> LIN_INT
    }

  logger.result("Using portfolio: $mainTrait\n")

  val inProcessStm = getStm(mainTrait, true)
  val notInProcessStm = getStm(mainTrait, false)

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(mainTrait, false)
  else STM(inProcess, setOf(fallbackEdge))
}
