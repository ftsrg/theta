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
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.params.Refinement.BW_BIN_ITP
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.collectVars

fun chcCompPortfolio25(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): STM {
  val checker = { config: XcfaConfig<*, *> -> runConfig(config, logger, uniqueLogger, true) }

  val baseCegarConfig = baseCegarConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseBoundedConfig = baseBoundedConfig(xcfa, mcm, parseContext, portfolioConfig, false)
  val baseMddConfig = baseMddConfig(xcfa, mcm, parseContext, portfolioConfig, false)

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    val bool = { timeout: Long, solver: String ->
      ConfigNode(
        "PredBool-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_BOOL,
          refinement = BW_BIN_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
        ),
        checker,
      )
    }
    val cart = { timeout: Long, solver: String ->
      ConfigNode(
        "PredCart-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_CART,
          refinement = BW_BIN_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
        ),
        checker,
      )
    }

    val expl = { timeout: Long, solver: String ->
      ConfigNode(
        "Expl-$inProcess",
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = EXPL,
          refinement = Refinement.SEQ_ITP,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
        ),
        checker,
      )
    }

    val bmc = { timeout: Long, solver: String ->
      ConfigNode(
        "BMC-$inProcess",
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
        "KIND-$inProcess",
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
        "IMC-$inProcess",
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

    val mdd = { timeout: Long ->
      ConfigNode(
        "MDD-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
            )
        ),
        checker,
      )
    }

    val mddCegar = { timeout: Long ->
      ConfigNode(
        "MDD-cegar-$inProcess",
        baseMddConfig.copy(
          backendConfig =
            baseMddConfig.backendConfig.copy(
              timeoutMs = timeout,
              inProcess = inProcess,
              parseInProcess = true,
              specConfig = baseMddConfig.backendConfig.specConfig!!.copy(cegar = true),
            )
        ),
        checker,
      )
    }

    val complex25 =
      ConfigNode(
        "Complex25-$inProcess",
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
              specConfig = PortfolioConfig("COMPLEX25")
            ),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
        ),
        checker,
      )

    val types = xcfa.collectVars().map { it.type }.toSet()

    infix fun ConfigNode.then(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, if (inProcess) anythingButServerError else anyError))
      return node
    }

    val (startingConfig, endConfig) =
      if (xcfa.isInlined) {
        if (types.any { it is BvType }) {
          // BV-Lin
          val bmc = bmc(450_000, "Z3")
          val kind = kind(20_000, "Z3")
          val expl = expl(650_000, "Z3")
          val bmcCVC5 = bmc(550_000, "cvc5:1.0.8")
          val imc = imc(10_000, "mathsat:5.6.10")
          val bool = bool(15_000, "Z3")
          val cart = cart(15_000, "Z3")
          val kindCVC5 = kind(70_000, "cvc5:1.0.8")
          val boolCVC5 = bool(70_000, "cvc5:1.0.8")
          val cartCVC5 = cart(500_000, "cvc5:1.0.8")
          val explCVC5 = expl(125_000, "cvc5:1.0.8")
          val mdd = mdd(100_000)
          val mddCegar = mddCegar(100_000)

          kind then
            imc then
            bool then
            cart then
            mddCegar then
            kindCVC5 then
            boolCVC5 then
            bmc then
            explCVC5 then
            bmcCVC5 then
            expl then
            cartCVC5 then
            mdd

          Pair(kind, mdd)
        } else if (types.any { it is RatType }) {
          // LRA-Lin
          val bmc = bmc(150_000, "Z3")
          val kind = kind(200_000, "Z3")
          val bool = bool(300_000, "Z3")
          val cart = cart(450_000, "Z3")
          val imc = imc(15_000, "mathsat:5.6.10")
          val cartCVC5 = cart(600_000, "cvc5:1.0.8")
          val expl = expl(10_000, "Z3")
          val mdd = mdd(50_000)
          val mddCegar = mddCegar(100_000)

          bmc then kind then bool then cart then imc then mddCegar then cartCVC5 then expl then mdd

          Pair(bmc, mdd)
        } else if (types.any { it is ArrayType<*, *> }) {
          // LIA-Arrays-Lin
          val cart = cart(25_000, "Z3")
          val bool = bool(10_000, "Z3")
          val expl = expl(10_000, "Z3")
          val imc = imc(20_000, "mathsat:5.6.10")
          val kind = kind(10_000, "Z3")
          val bmc = bmc(400_000, "Z3")
          val mdd = mdd(50_000)
          val mddCegar = mddCegar(100_000)

          cart then bool then expl then imc then kind then bmc then mddCegar then mdd

          Pair(cart, mdd)
        } else {
          // LIA-Lin
          val cart = cart(500_000, "Z3")
          val bool = bool(150_000, "Z3")
          val bmc = bmc(20_000, "Z3")
          val imc = imc(20_000, "mathsat:5.6.10")
          val kind = kind(20_000, "Z3")
          val expl = expl(50_000, "Z3")
          val boolCVC5 = bool(700_000, "cvc5:1.0.8")
          val cartCVC5 = cart(550_000, "cvc5:1.0.8")
          val mdd = mdd(75_000)
          val imcCVC5 = imc(50_000, "cvc5:1.0.8")
          val explCVC5 = expl(50_000, "cvc5:1.0.8")
          val bmcCVC5 = bmc(100_000, "cvc5:1.0.8")
          val mddCegar = mddCegar(100_000)

          bmc then
            imc then
            kind then
            expl then
            mdd then
            mddCegar then
            imcCVC5 then
            explCVC5 then
            cart then
            bool then
            boolCVC5 then
            cartCVC5 then
            bmcCVC5

          Pair(bmc, bmcCVC5)
        }
      } else {
        val expl = expl(600_000, "Z3")
        val bool = bool(600_000, "Z3")
        val cart = cart(600_000, "Z3")
        val explCVC5 = expl(600_000, "cvc5:1.0.8")
        val boolCVC5 = bool(600_000, "cvc5:1.0.8")
        val cartCVC5 = cart(600_000, "cvc5:1.0.8")

        expl then bool then cart then explCVC5 then boolCVC5 then cartCVC5

        Pair(expl, cartCVC5)
      }

    endConfig then complex25

    return STM(startingConfig, edges)
  }

  val inProcessStm = getStm(true)
  val notInProcessStm = getStm(false)

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(false)
  else STM(inProcess, setOf(fallbackEdge))
}
