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
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
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
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.UnrollPass
import hu.bme.mit.theta.xcfa.utils.dereferences

/**
 * Per-configuration slices of the 900 s budget.
 *
 * Sized from a 16-configuration sweep of the whole suite: 80 % of every configuration's correct
 * answers arrive within 16 s and 95 % within 25-120 s, so a long slice buys very little while a
 * configuration that never gets a slice costs everything it would have solved. Breadth first, and
 * only the leader gets an extended second attempt. The previous chain spent 300+300+200+150 ms =
 * 950 s of slices inside a 900 s limit, so its last configuration could never run at all.
 */
private const val LEAD_SLICE_MS = 150_000L
private const val NEXT_SLICE_MS = 100_000L
private const val RETRY_SLICE_MS = 200_000L

fun complex27(
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

  fun getStm(mainTrait: MainTrait, loopFree: Boolean, inProcess: Boolean): STM {
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

    /**
     * The leading configuration again, but with the program re-read under bitvector arithmetic.
     *
     * `efficient` resolves to integer wherever integer can express the program, and that is the
     * right first bet: on the tasks both encodings can parse, integer solves more than bitvector in
     * every algorithm measured, and solves it faster. It is not a free win though -- bitvector
     * still decides several hundred tasks per algorithm that integer cannot -- so once the integer
     * attempt is spent, the last slice pays for a re-parse and tries the other encoding.
     *
     * Interpolation has to move with the encoding: Z3's legacy API refuses to interpolate
     * bitvectors, so this configuration interpolates on MathSAT whatever the rest of the chain
     * uses.
     */
    fun bitvectorRetry(timeout: Long, solver: String): ConfigNode {
      val adapted =
        baseCegarConfig.adaptConfig(
          inProcess = inProcess,
          domain = PRED_CART,
          refinement = Refinement.BW_BIN_ITP,
          exprSplitter = ExprSplitterOptions.WHOLE,
          timeoutMs = timeout,
          abstractionSolver = solver,
          refinementSolver = solver,
        )
      return ConfigNode(
        "PRED_CART-BW_BIN_ITP-bitvector-$solver-$inProcess",
        XcfaConfig<CFrontendConfig, CegarConfig>(
          inputConfig =
            portfolioConfig.inputConfig.copy(
              xcfaWCtx = null, // re-read the program: the parsed one is integer-encoded
              propertyFile = null,
              property = portfolioConfig.inputConfig.property,
            ),
          frontendConfig =
            FrontendConfig(
              lbeLevel = LbePass.defaultLevel,
              loopUnroll = UnrollPass.UNROLL_LIMIT,
              inputType = InputType.C,
              specConfig = CFrontendConfig(arithmetic = ArithmeticType.bitvector),
            ),
          backendConfig = adapted.backendConfig.copy(parseInProcess = true),
          outputConfig = baseCegarConfig.outputConfig,
          debugConfig = portfolioConfig.debugConfig,
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

    /**
     * One step of the chain: a configuration and the same configuration on a different solver.
     *
     * A solver failure says nothing about whether the *next algorithm* would work -- it is a
     * property of the solver, not of the program -- so it must not consume the next step's slice.
     * The twin absorbs it and rejoins the chain where the primary left off.
     */
    fun step(make: (Long, String) -> ConfigNode, ms: Long, solver: String, alt: String) =
      make(ms, solver) to make(ms, alt)

    fun wire(steps: List<Pair<ConfigNode, ConfigNode>>) {
      steps.zipWithNext { (primary, _), (next, _) -> primary then next }
      steps.forEach { (primary, twin) -> primary onSolverError twin }
      steps.zipWithNext { (_, twin), (next, _) -> twin then next }
    }

    // Which solver each kind of configuration runs on, and what it falls back to.
    //
    // This is decided by the theories the program actually contains, not by which chain it takes.
    // The two are independent: `mainTrait` picks the *order* of algorithms, but the encoding comes
    // from the frontend, and a pointer-manipulating program full of bitwise operators is encoded
    // over bitvectors while still being routed down the pointer chain. Keying the solver off the
    // chain sent exactly those programs to Z3, whose legacy API is the only Z3 that interpolates
    // and which refuses bitvectors outright ("theory not supported by interpolation").
    //
    // Floats outrank bitvectors here: MathSAT rejects the combination with
    // "FP<->BV combination unsupported by the current configuration", so a program with both has to
    // go to cvc5, which decides them together.
    val bitvectorEncoded =
      parseContext.arithmetic == ArithmeticType.bitvector ||
        ArithmeticTrait.BITWISE in parseContext.arithmeticTraits
    val hasFloats = ArithmeticTrait.FLOAT in parseContext.arithmeticTraits

    val itpSolver: String
    val itpAlt: String
    val bmcSolver: String
    val bmcAlt: String
    when {
      hasFloats -> {
        itpSolver = "cvc5:1.2.0"
        // Falling back to MathSAT is only safe while there are no bitvectors to combine floats
        // with; when there are, stay inside the family that decides the combination at all.
        itpAlt = if (bitvectorEncoded) "cvc5:1.0.8" else "mathsat:5.6.12"
        bmcSolver = "cvc5:1.2.0"
        bmcAlt = "Z3:new"
      }
      bitvectorEncoded -> {
        itpSolver = "mathsat:5.6.12"
        itpAlt = "mathsat:5.6.10"
        bmcSolver = "Z3:new"
        bmcAlt = "mathsat:5.6.12"
      }
      else -> {
        itpSolver = "Z3"
        itpAlt = "mathsat:5.6.12"
        bmcSolver = "Z3:new"
        bmcAlt = "mathsat:5.6.12"
      }
    }

    val lead = { ms: Long, solver: String -> cegar(ms, solver, PRED_CART, Refinement.BW_BIN_ITP) }
    val explSeq = { ms: Long, solver: String -> cegar(ms, solver, EXPL, Refinement.SEQ_ITP) }
    val predSeq = { ms: Long, solver: String -> cegar(ms, solver, PRED_CART, Refinement.SEQ_ITP) }

    val (startingConfig, endConfig) =
      if (xcfa.isInlined) {
        when (mainTrait) {
          MULTITHREAD -> multithread to multithread
          TERMINATION -> termination to termination
          else -> {
            val predCartBw = step(lead, LEAD_SLICE_MS, itpSolver, itpAlt)
            val boundedBmc = step(bmc, NEXT_SLICE_MS, bmcSolver, bmcAlt)
            val explicitSeq = step(explSeq, NEXT_SLICE_MS, itpSolver, itpAlt)
            val boundedKind = step(kind, NEXT_SLICE_MS, bmcSolver, bmcAlt)
            val predCartSeq = step(predSeq, NEXT_SLICE_MS, itpSolver, itpAlt)

            // Bounded engines lead when they are the ones that can *finish*: with no cycle in any
            // procedure every execution is finite, so a bounded check that reaches the longest path
            // has proved safety. Non-linear arithmetic leads with them for the opposite reason --
            // interpolation over non-linear terms is where the refinement loop stalls, so the
            // engines that never interpolate get their slice before the ones that do.
            val steps =
              if (loopFree || mainTrait == NONLIN_INT)
                listOf(boundedBmc, boundedKind, predCartBw, explicitSeq, predCartSeq)
              else listOf(predCartBw, boundedBmc, explicitSeq, boundedKind, predCartSeq)

            wire(steps)

            // The last slice changes the encoding rather than the algorithm. Past this point
            // another algorithm is worth tens of tasks, while the encoding the frontend did not
            // pick is worth several hundred per algorithm. It is skipped where it cannot pay:
            // `efficient` already resolves to bitvector for a bitwise program, so re-parsing would
            // reproduce the same XCFA, and a float program has no bitvector encoding at all.
            val lastResort =
              if (bitvectorEncoded || hasFloats) lead(RETRY_SLICE_MS, itpAlt)
              else bitvectorRetry(RETRY_SLICE_MS, "mathsat:5.6.12")
            steps.last().first then lastResort
            steps.last().second then lastResort

            steps.first().first to lastResort
          }
        }
      } else {
        // Not inlined: recursion survived, so the bounded engines cannot bound it and only the
        // CEGAR configurations are applicable.
        val steps =
          listOf(
            step(lead, LEAD_SLICE_MS, itpSolver, itpAlt),
            step(explSeq, NEXT_SLICE_MS, itpSolver, itpAlt),
            step(predSeq, NEXT_SLICE_MS, itpSolver, itpAlt),
          )
        wire(steps)
        val lastResort = lead(RETRY_SLICE_MS, itpAlt)
        steps.last().first then lastResort
        steps.last().second then lastResort
        steps.first().first to lastResort
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

  logger.benchmark("Using portfolio: $mainTrait\n")

  val loopFree = xcfa.boundedIsComplete
  logger.benchmark("Bounded engines complete: $loopFree\n")

  val inProcessStm = getStm(mainTrait, loopFree, true)
  val notInProcessStm = getStm(mainTrait, loopFree, false)

  val inProcess = HierarchicalNode("InProcess", inProcessStm)
  val notInProcess = HierarchicalNode("NotInprocess", notInProcessStm)

  val fallbackEdge = Edge(inProcess, notInProcess, ExceptionTrigger(label = "Anything"))

  return if (portfolioConfig.debugConfig.debug) getStm(mainTrait, loopFree, false)
  else STM(inProcess, setOf(fallbackEdge))
}
