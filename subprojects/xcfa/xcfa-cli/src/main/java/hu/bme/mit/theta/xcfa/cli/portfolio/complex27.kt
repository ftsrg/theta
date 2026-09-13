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
    // Interpolation is the binding constraint. Z3's legacy API is the only Z3 that interpolates at
    // all, and it refuses bitvectors outright ("theory not supported by interpolation"), so a
    // bitwise program has to interpolate on MathSAT from the first step rather than rediscover this
    // one configuration at a time. Floats are the mirror image: cvc5 decides them, so it leads and
    // Z3 backs it up.
    val itpSolver: String
    val itpAlt: String
    val bmcSolver: String
    val bmcAlt: String
    when (mainTrait) {
      FLOAT -> {
        itpSolver = "cvc5:1.2.0"; itpAlt = "Z3"; bmcSolver = "cvc5:1.2.0"; bmcAlt = "Z3:new"
      }
      BITWISE -> {
        itpSolver = "mathsat:5.6.12"; itpAlt = "mathsat:5.6.10"
        bmcSolver = "Z3:new"; bmcAlt = "mathsat:5.6.12"
      }
      else -> {
        itpSolver = "Z3"; itpAlt = "mathsat:5.6.12"
        bmcSolver = "Z3:new"; bmcAlt = "mathsat:5.6.12"
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

            // Whatever budget is left goes back to the strongest configuration rather than to a
            // sixth algorithm: past this point the measured marginal gain of another algorithm is
            // in the tens of tasks, while the leader still has answers arriving well beyond its
            // first slice.
            val lastResort = lead(RETRY_SLICE_MS, itpAlt)
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
