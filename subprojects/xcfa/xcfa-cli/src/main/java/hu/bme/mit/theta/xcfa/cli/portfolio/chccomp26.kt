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
 * 1. Explicit `--chc-category` value (anything other than AUTO)
 * 2. Variable-type + linearity auto-detection: non-inlined CHC (nonlinear clauses) maps to BV / LIA
 *    / LIA_ARRAYS; inlined (linear) CHC maps to BV_LIN / LIA_LIN / LIA_LIN_ARRAYS / LRA_LIN based
 *    on variable types.
 *
 * Note: AUTO cannot distinguish LRA from LRA_LIN, or exact BV/LIA sub-variants. When the
 * competition infrastructure passes the exact category name via `--chc-category`, the portfolio can
 * select the optimal chain for every category.
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
  // When auto-detecting, non-inlined CHC (nonlinear clauses) maps to the corresponding
  // non-linear category variant; inlined (linear) CHC maps to the linear variant.
  val types = xcfa.collectVars().map { it.type }.toSet()
  val category =
    if (categoryHint != AUTO) categoryHint
    else {
      val detectedLinear =
        when {
          types.any { it is BvType } -> BV_LIN
          types.any { it is RatType } -> LRA_LIN
          types.any { it is ArrayType<*, *> } -> LIA_LIN_ARRAYS
          else -> LIA_LIN
        }
      if (!xcfa.isInlined)
        when (detectedLinear) {
          BV_LIN -> BV
          LIA_LIN -> LIA
          LIA_LIN_ARRAYS -> LIA_ARRAYS
          else -> detectedLinear
        }
      else detectedLinear
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
          refinement = Refinement.SEQ_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
          search = Search.ERR,
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
          refinement = Refinement.SEQ_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
          search = Search.ERR,
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
          search = Search.ERR,
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

    infix fun ConfigNode.then(node: ConfigNode): ConfigNode {
      edges.add(Edge(this, node, if (inProcess) anythingButServerError else anyError))
      return node
    }

    // ── Category-specific chains ────────────────────────────────────────────
    // Each chain is sized to fit within the 30-minute (1 800 000 ms) wall-clock budget.

    val (startingConfig, endConfig) =
      if (needsModel) {
        // ── Model-validation portfolio ──────────────────────────────────────
        // Prioritise configurations that produce externally verifiable witnesses:
        //   IC3 / MDD (100 % validation), IMC-MS (~98 %), CEGAR-CART in linear categories (~100 %).
        // BMC and KIND are placed last in categories where they yield 0 % validation.
        when (category) {
          BV -> {
            // BV (nonlinear): CEGAR-only — non-CEGAR techniques are ineffective on nonlinear CHCs.
            // No Z3 for interpolating configs on BV: use MathSAT then cvc5.
            val c1 = cart(600_000, "mathsat:5.6.10")
            val c2 = bool(400_000, "mathsat:5.6.10")
            val c3 = bool(400_000, "cvc5:1.0.8")
            val c4 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4
            Pair(c1, c4)
          }

          BV_LIN -> {
            // IC3 dominates for BV-Lin models; IMC-MS and CART-MS bridge the remaining gap.
            val c1 = ic3(200_000, "Z3")
            val c2 = ic3(200_000, "mathsat:5.6.10")
            val c3 = imc(300_000, "mathsat:5.6.10")
            val c4 = cart(400_000, "mathsat:5.6.10")
            val c5 = bool(300_000, "mathsat:5.6.10")
            val c6 = cart(400_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6
            Pair(c1, c6)
          }

          LIA,
          LIA_ARRAYS -> {
            // All CEGAR configs produce 0 % validated witnesses here.
            // Use the same order as the solving portfolio to maximise solved count.
            val c1 = cart(900_000, "Z3")
            val c2 = cart(400_000, "mathsat:5.6.10")
            val c3 = bool(300_000, "Z3")
            val c4 = expl(200_000, "Z3")
            val c5 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5
            Pair(c1, c5)
          }

          LIA_LIN -> {
            // MDD and IMC-MS produce near-perfectly validated witnesses; CEGAR-CART follows.
            val c1 = mdd(150_000)
            val c2 = imc(200_000, "mathsat:5.6.10")
            val c3 = cart(600_000, "Z3")
            val c4 = bool(400_000, "Z3")
            val c5 = imc(200_000, "Z3")
            val c6 = cart(250_000, "mathsat:5.6.10")
            val c7 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6 then c7
            Pair(c1, c7)
          }

          LIA_LIN_ARRAYS -> {
            // IMC does not handle arrays; rely on MDD (if applicable) and CEGAR.
            val c1 = mdd(150_000)
            val c2 = cart(800_000, "Z3")
            val c3 = bool(500_000, "Z3")
            val c4 = bmc(200_000, "Z3")
            val c5 = expl(150_000, "Z3")
            val c6 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6
            Pair(c1, c6)
          }

          LRA_LIN -> {
            // CEGAR-CART-MS: 100 % validated. BMC/KIND: 0 % validated — placed last.
            val c1 = cart(600_000, "mathsat:5.6.10")
            val c2 = imc(300_000, "mathsat:5.6.10")
            val c3 = cart(400_000, "Z3")
            val c4 = kind(300_000, "Z3")
            val c5 = bmc(200_000, "Z3")
            val c6 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6
            Pair(c1, c6)
          }

          AUTO -> error("Category should have been resolved before this point")
        }
      } else {
        // ── Solving portfolio ───────────────────────────────────────────────
        // Order: fastest/most-effective first per category, then complementary configs.
        when (category) {
          BV -> {
            // BV (nonlinear): CEGAR-only — non-CEGAR techniques are ineffective on nonlinear CHCs.
            // No Z3 for interpolating configs on BV: use MathSAT then cvc5.
            val c1 = expl(600_000, "mathsat:5.6.10")
            val c2 = bool(600_000, "mathsat:5.6.10")
            val c3 = cart(600_000, "mathsat:5.6.10")
            val c4 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4
            Pair(c1, c4)
          }

          BV_LIN -> {
            // CART-MS dominates (58); IMC-MS, BOOL-MS, KIND bridge the remaining gap to 77.
            val c1 = cart(300_000, "mathsat:5.6.10")
            val c2 = bool(200_000, "mathsat:5.6.10")
            val c3 = imc(100_000, "mathsat:5.6.10")
            val c4 = kind(250_000, "Z3")
            val c5 = kind(400_000, "cvc5:1.0.8")
            val c6 = cart(550_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6
            Pair(c1, c6)
          }

          LIA -> {
            // CART-Z3 and CART-MS are nearly equal at the top; BOOL and EXPL add coverage.
            val c1 = cart(900_000, "Z3")
            val c2 = cart(400_000, "mathsat:5.6.10")
            val c3 = bool(300_000, "Z3")
            val c4 = expl(200_000, "Z3")
            val c5 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5
            Pair(c1, c5)
          }

          LIA_ARRAYS -> {
            // CART-Z3 solves 99 % of the solvable instances; a short EXPL pass covers the rest.
            val c1 = cart(1_600_000, "Z3")
            val c2 = expl(200_000, "Z3")
            val c3 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3
            Pair(c1, c3)
          }

          LIA_LIN -> {
            // IMC-MS and bounded techniques provide quick wins; CART and BOOL cover the bulk.
            val c1 = imc(60_000, "mathsat:5.6.10")
            val c2 = bmc(30_000, "Z3")
            val c3 = kind(30_000, "Z3")
            val c4 = cart(550_000, "Z3")
            val c5 = bool(400_000, "Z3")
            val c6 = cart(380_000, "mathsat:5.6.10")
            val c7 = bool(350_000, "cvc5:1.0.8")
            val c8 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6 then c7 then c8
            Pair(c1, c8)
          }

          LIA_LIN_ARRAYS -> {
            // CART-Z3 covers 93 % of solvable instances; bounded techniques fill the gap.
            val c1 = cart(800_000, "Z3")
            val c2 = imc(100_000, "mathsat:5.6.10")
            val c3 = bmc(200_000, "Z3")
            val c4 = bool(500_000, "Z3")
            val c5 = expl(200_000, "Z3")
            val c6 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6
            Pair(c1, c6)
          }

          LRA_LIN -> {
            // BMC and KIND tied at top; CART-MS and IMC-MS provide complementary coverage.
            val c1 = bmc(150_000, "Z3")
            val c2 = kind(300_000, "Z3")
            val c3 = cart(600_000, "mathsat:5.6.10")
            val c4 = imc(300_000, "mathsat:5.6.10")
            val c5 = cart(450_000, "Z3")
            val c6 = cart(200_000, "cvc5:1.0.8")
            c1 then c2 then c3 then c4 then c5 then c6
            Pair(c1, c6)
          }

          AUTO -> error("Category should have been resolved before this point")
        }
      }

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
