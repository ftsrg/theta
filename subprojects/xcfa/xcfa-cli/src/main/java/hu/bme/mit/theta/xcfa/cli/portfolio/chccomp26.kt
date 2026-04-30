/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.xcfa.cli.params.ChcCategory.*
import hu.bme.mit.theta.xcfa.cli.params.Domain.*
import hu.bme.mit.theta.xcfa.cli.params.Refinement.BW_BIN_ITP
import hu.bme.mit.theta.xcfa.cli.runConfig
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.collectVars

/**
 * CHC-COMP 2026 portfolio.
 *
 * Uses an explicit category hint (`--chc-category`) when provided, or falls back to type-based
 * auto-detection when the category is `AUTO`. Within each category a separate, empirically tuned
 * configuration sequence is run for plain solving vs. model-generation mode (`--print-model`).
 *
 * Time budget: 30 minutes (1 800 000 ms) split across configurations in each category chain.
 *
 * Category detection precedence:
 *  1. Explicit `--chc-category` value (anything other than AUTO)
 *  2. Variable-type auto-detection (BvType → BV_LIN, RatType → LRA_LIN,
 *     ArrayType → LIA_LIN_ARRAYS, otherwise LIA_LIN)
 *
 * Note: AUTO cannot distinguish BV from BV_LIN, or LIA/LIA_ARRAYS from LIA_LIN/LIA_LIN_ARRAYS.
 * When the competition infrastructure passes the exact category name via `--chc-category`, the
 * portfolio can select the optimal chain for every category.
 */
fun chcCompPortfolio26(
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
  val baseIc3Config = baseIc3Config(xcfa, mcm, parseContext, portfolioConfig, false)

  val chcFrontend = portfolioConfig.frontendConfig.specConfig as? CHCFrontendConfig
  val needsModel = chcFrontend?.model ?: false
  val categoryHint = chcFrontend?.category ?: AUTO

  // Resolve effective category: explicit hint wins over type-based detection.
  val types = xcfa.collectVars().map { it.type }.toSet()
  val category =
    if (categoryHint != AUTO) categoryHint
    else
      when {
        types.any { it is BvType } -> BV_LIN
        types.any { it is RatType } -> LRA_LIN
        types.any { it is ArrayType<*, *> } -> LIA_LIN_ARRAYS
        else -> LIA_LIN
      }

  fun getStm(inProcess: Boolean): STM {
    val edges = LinkedHashSet<Edge>()

    // ── Configuration builders ──────────────────────────────────────────────

    val cart = { timeout: Long, solver: String ->
      ConfigNode(
        "PredCart-$solver-$inProcess",
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

    val bool = { timeout: Long, solver: String ->
      ConfigNode(
        "PredBool-$solver-$inProcess",
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

    val expl = { timeout: Long, solver: String ->
      ConfigNode(
        "Expl-$solver-$inProcess",
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
        "BMC-$solver-$inProcess",
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
        "KIND-$solver-$inProcess",
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
        "IMC-$solver-$inProcess",
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

    val ic3 = { timeout: Long, solver: String ->
      ConfigNode(
        "IC3-$solver-$inProcess",
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

    val complex26 =
      ConfigNode(
        "Complex26-$inProcess",
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

    infix fun ConfigNode.then(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, if (inProcess) anythingButServerError else anyError))
      return node
    }

    // ── Category-specific chains ────────────────────────────────────────────
    // Each chain is sized to fit within the 30-minute (1 800 000 ms) wall-clock budget.

    val (startingConfig, endConfig) =
      if (!xcfa.isInlined) {
        // Non-inlined CHC (procedure calls present): use generic CEGAR chain.
        val chain =
          cart(600_000, "Z3") then
            bool(600_000, "Z3") then
            cart(600_000, "cvc5:1.0.8")
        Pair(chain, cart(600_000, "cvc5:1.0.8"))
      } else if (needsModel) {
        // ── Model-validation portfolio ──────────────────────────────────────
        // Prioritise configurations that produce externally verifiable witnesses:
        //   IC3 / MDD (100 % validation), IMC-MS (~98 %), CEGAR-CART in linear categories (~100 %).
        // BMC and KIND are placed last in categories where they yield 0 % validation.
        when (category) {
          BV_LIN, BV -> {
            // IC3 dominates for BV-Lin models; IMC-MS and CART-MS bridge the remaining gap.
            val start =
              ic3(200_000, "Z3") then
                ic3(200_000, "mathsat:5.6.10") then
                imc(300_000, "mathsat:5.6.10") then
                cart(400_000, "mathsat:5.6.10") then
                bool(300_000, "mathsat:5.6.10") then
                kind(400_000, "cvc5:1.0.8")
            Pair(start, kind(400_000, "cvc5:1.0.8"))
          }

          LIA, LIA_ARRAYS -> {
            // All CEGAR configs produce 0 % validated witnesses here (quantified invariants).
            // Use the same order as the solving portfolio to maximise solved count.
            val start =
              cart(900_000, "Z3") then
                cart(400_000, "mathsat:5.6.10") then
                bool(300_000, "Z3") then
                expl(200_000, "Z3")
            Pair(start, expl(200_000, "Z3"))
          }

          LIA_LIN -> {
            // MDD and IMC-MS produce near-perfectly validated witnesses; CEGAR-CART follows.
            val start =
              mdd(150_000) then
                imc(200_000, "mathsat:5.6.10") then
                cart(600_000, "Z3") then
                bool(400_000, "Z3") then
                imc(200_000, "Z3") then
                cart(250_000, "mathsat:5.6.10")
            Pair(start, cart(250_000, "mathsat:5.6.10"))
          }

          LIA_LIN_ARRAYS -> {
            // IMC does not handle arrays; rely on MDD (if applicable) and CEGAR.
            val start =
              mdd(150_000) then
                cart(800_000, "Z3") then
                bool(500_000, "Z3") then
                bmc(200_000, "Z3") then
                expl(150_000, "Z3")
            Pair(start, expl(150_000, "Z3"))
          }

          LRA_LIN -> {
            // CEGAR-CART-MS: 100 % validated. BMC/KIND: 0 % validated — placed last.
            val start =
              cart(600_000, "mathsat:5.6.10") then
                imc(300_000, "mathsat:5.6.10") then
                cart(400_000, "Z3") then
                kind(300_000, "Z3") then
                bmc(200_000, "Z3")
            Pair(start, bmc(200_000, "Z3"))
          }

          AUTO -> error("Category should have been resolved before this point")
        }
      } else {
        // ── Solving portfolio ───────────────────────────────────────────────
        // Order: fastest/most-effective first per category, then complementary configs.
        when (category) {
          BV -> {
            // All CEGAR variants solve 3/68; no bounded technique applies.
            val start =
              expl(600_000, "Z3") then bool(600_000, "Z3") then cart(600_000, "Z3")
            Pair(start, cart(600_000, "Z3"))
          }

          BV_LIN -> {
            // CART-MS dominates (58); IMC-MS, BOOL-MS, KIND bridge the remaining gap to 77.
            val start =
              cart(300_000, "mathsat:5.6.10") then
                bool(200_000, "mathsat:5.6.10") then
                imc(100_000, "mathsat:5.6.10") then
                kind(250_000, "Z3") then
                kind(400_000, "cvc5:1.0.8") then
                cart(550_000, "cvc5:1.0.8")
            Pair(start, cart(550_000, "cvc5:1.0.8"))
          }

          LIA -> {
            // CART-Z3 and CART-MS are nearly equal at the top; BOOL and EXPL add coverage.
            val start =
              cart(900_000, "Z3") then
                cart(400_000, "mathsat:5.6.10") then
                bool(300_000, "Z3") then
                expl(200_000, "Z3")
            Pair(start, expl(200_000, "Z3"))
          }

          LIA_ARRAYS -> {
            // CART-Z3 solves 99 % of the solvable instances; a short EXPL pass covers the rest.
            val start = cart(1_600_000, "Z3") then expl(200_000, "Z3")
            Pair(start, expl(200_000, "Z3"))
          }

          LIA_LIN -> {
            // IMC-MS and bounded techniques provide quick wins; CART and BOOL cover the bulk.
            val start =
              imc(60_000, "mathsat:5.6.10") then
                bmc(30_000, "Z3") then
                kind(30_000, "Z3") then
                cart(550_000, "Z3") then
                bool(400_000, "Z3") then
                cart(380_000, "mathsat:5.6.10") then
                bool(350_000, "cvc5:1.0.8")
            Pair(start, bool(350_000, "cvc5:1.0.8"))
          }

          LIA_LIN_ARRAYS -> {
            // CART-Z3 covers 93 % of solvable instances; bounded techniques fill the gap.
            val start =
              cart(800_000, "Z3") then
                imc(100_000, "mathsat:5.6.10") then
                bmc(200_000, "Z3") then
                bool(500_000, "Z3") then
                expl(200_000, "Z3")
            Pair(start, expl(200_000, "Z3"))
          }

          LRA_LIN -> {
            // BMC and KIND tied at top; CART-MS and IMC-MS provide complementary coverage.
            val start =
              bmc(150_000, "Z3") then
                kind(300_000, "Z3") then
                cart(600_000, "mathsat:5.6.10") then
                imc(300_000, "mathsat:5.6.10") then
                cart(450_000, "Z3")
            Pair(start, cart(450_000, "Z3"))
          }

          AUTO -> error("Category should have been resolved before this point")
        }
      }

    endConfig then complex26

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
