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

import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopCheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.FULL
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.LAZY
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection.ERROR_LOCATION
import hu.bme.mit.theta.xcfa.analysis.isInlined
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.Backend.CEGAR
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions.CHECK
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.COI
import hu.bme.mit.theta.xcfa.cli.params.ConeOfInfluenceMode.NO_COI
import hu.bme.mit.theta.xcfa.cli.params.Domain.EXPL
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes.SERVER_ERROR
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes.SOLVER_ERROR
import hu.bme.mit.theta.xcfa.cli.params.ExprSplitterOptions.WHOLE
import hu.bme.mit.theta.xcfa.cli.params.InitPrec.EMPTY
import hu.bme.mit.theta.xcfa.cli.params.POR.AASPOR
import hu.bme.mit.theta.xcfa.cli.params.POR.NOPOR
import hu.bme.mit.theta.xcfa.cli.params.POR.SPOR
import hu.bme.mit.theta.xcfa.cli.params.Refinement.SEQ_ITP
import hu.bme.mit.theta.xcfa.cli.params.Search.BFS
import hu.bme.mit.theta.xcfa.cli.params.Search.DFS
import hu.bme.mit.theta.xcfa.cli.params.Search.ERR
import hu.bme.mit.theta.xcfa.model.XCFA
import java.nio.file.Files
import java.nio.file.Path

fun baseCegarConfig(
  xcfa: XCFA,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
): XcfaConfig<*, CegarConfig> {
  var baseConfig =
    XcfaConfig(
      inputConfig = portfolioConfig.inputConfig,
      frontendConfig = portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>,
      backendConfig =
        BackendConfig(
          backend = CEGAR,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          specConfig =
            CegarConfig(
              initPrec = EMPTY,
              por = NOPOR,
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
      outputConfig = getDefaultOutputConfig(portfolioConfig),
      debugConfig = portfolioConfig.debugConfig,
    )

  if (parseContext.multiThreading) {
    val baseCegarConfig = baseConfig.backendConfig.specConfig!!
    val verifiedProperty = baseConfig.inputConfig.property.verifiedProperty
    val multiThreadedCegarConfig =
      baseCegarConfig.copy(
        coi = if (verifiedProperty == ERROR_LOCATION) COI else NO_COI,
        por = if (verifiedProperty == ERROR_LOCATION) AASPOR else SPOR,
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = DFS),
      )
    baseConfig =
      baseConfig.copy(
        backendConfig = baseConfig.backendConfig.copy(specConfig = multiThreadedCegarConfig)
      )
  } else if (!xcfa.isInlined) {
    val baseCegarConfig = baseConfig.backendConfig.specConfig!!
    val recursiveConfig =
      baseCegarConfig.copy(
        abstractorConfig = baseCegarConfig.abstractorConfig.copy(search = BFS),
        refinerConfig = baseCegarConfig.refinerConfig.copy(pruneStrategy = LAZY),
      )
    baseConfig =
      baseConfig.copy(backendConfig = baseConfig.backendConfig.copy(specConfig = recursiveConfig))
  }
  return baseConfig
}

val timeoutOrNotSolvableError =
  ExceptionTrigger(
    fallthroughExceptions =
      setOf(ErrorCodeException(SOLVER_ERROR.code), ErrorCodeException(SERVER_ERROR.code)),
    label = "TimeoutOrNotSolvableError",
  )

val anythingButServerError =
  ExceptionTrigger(
    fallthroughExceptions = setOf(ErrorCodeException(SERVER_ERROR.code)),
    label = "AnythingButServerError",
  )

val solverError = ExceptionTrigger(ErrorCodeException(SOLVER_ERROR.code), label = "SolverError")

val anyError = ExceptionTrigger(label = "Anything")

/**
 * One step of a portfolio chain: the configuration built by [make] on [solver], paired with the
 * same configuration on [alt], its twin that takes over when the solver fails. When [alt] is
 * [solver] there is nothing to retry on, and the step is paired with itself.
 */
fun <N : Node> step(make: (Long, String) -> N, timeoutMs: Long, solver: String, alt: String) =
  make(timeoutMs, solver).let { it to if (alt == solver) it else make(timeoutMs, alt) }

/**
 * The edges that chain [steps] one after the other and end in [last]. A solver error moves a step
 * to its twin, and any failure of the twin moves on, so a solver failure costs no other step its
 * slice. Other failures move on to the next step; when [inProcess], only timeouts and unsolvable
 * tasks do.
 */
fun chainEdges(steps: List<Pair<Node, Node>>, last: Node, inProcess: Boolean): Set<Edge> {
  val next = if (inProcess) timeoutOrNotSolvableError else anyError
  val nextOrSolverError = if (inProcess) anythingButServerError else anyError
  val targets = steps.drop(1).map { it.first } + last
  return buildSet {
    steps.zip(targets).forEach { (step, target) ->
      val (primary, twin) = step
      if (twin === primary) {
        add(Edge(primary, target, nextOrSolverError))
      } else {
        add(Edge(primary, twin, solverError))
        add(Edge(primary, target, next))
        add(Edge(twin, target, nextOrSolverError))
      }
    }
  }
}

/**
 * [solver] at [version] if that version is installed in the solver home, otherwise its latest
 * installed version. Lets a portfolio keep the versions it was tuned with without failing on a
 * distribution that only ships newer ones.
 */
fun XcfaConfig<*, *>.solverVersionOrLatestFallback(solver: String, version: String): String =
  if (Files.isDirectory(Path.of(backendConfig.solverHome, solver, version))) "$solver:$version"
  else "$solver:latest"

fun XcfaConfig<*, CegarConfig>.adaptConfig(
  initPrec: InitPrec = this.backendConfig.specConfig!!.initPrec,
  timeoutMs: Long = this.backendConfig.timeoutMs,
  domain: Domain = this.backendConfig.specConfig!!.abstractorConfig.domain,
  refinement: Refinement = this.backendConfig.specConfig!!.refinerConfig.refinement,
  exprSplitter: ExprSplitterOptions = this.backendConfig.specConfig!!.refinerConfig.exprSplitter,
  abstractionSolver: String = this.backendConfig.specConfig!!.abstractorConfig.abstractionSolver,
  validateAbstractionSolver: Boolean =
    this.backendConfig.specConfig!!.abstractorConfig.validateAbstractionSolver,
  refinementSolver: String = this.backendConfig.specConfig!!.refinerConfig.refinementSolver,
  validateRefinementSolver: Boolean =
    this.backendConfig.specConfig!!.refinerConfig.validateRefinementSolver,
  coi: ConeOfInfluenceMode = this.backendConfig.specConfig!!.coi,
  search: Search = this.backendConfig.specConfig!!.abstractorConfig.search,
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
                  search = search,
                ),
            refinerConfig =
              backendConfig.specConfig!!
                .refinerConfig
                .copy(
                  refinementSolver = refinementSolver,
                  validateRefinementSolver = validateRefinementSolver,
                  refinement = refinement,
                  exprSplitter = exprSplitter,
                ),
            coi = coi,
          ),
      )
  )
}

fun baseAsgCegarConfig(
  portfolioConfig: XcfaConfig<*, *>
): XcfaConfig<SpecFrontendConfig, AsgCegarConfig> =
  XcfaConfig(
    inputConfig = portfolioConfig.inputConfig,
    frontendConfig = portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>,
    backendConfig =
      BackendConfig(
        backend = Backend.LIVENESS_CEGAR,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        specConfig =
          AsgCegarConfig(
            initPrec = EMPTY,
            cexMonitor = CHECK,
            abstractorConfig =
              AsgCegarAbstractorConfig(
                abstractionSolver = "Z3",
                validateAbstractionSolver = false,
                domain = EXPL,
                maxEnum = 1,
                search = LoopCheckerSearchStrategy.NDFS,
              ),
            refinerConfig =
              AsgCegarRefinerConfig(
                refinementSolver = "Z3",
                validateRefinementSolver = false,
                refinement = ASGTraceCheckerStrategy.DIRECT_REFINEMENT,
                exprSplitter = WHOLE,
              ),
          ),
      ),
    outputConfig = getDefaultOutputConfig(portfolioConfig),
    debugConfig = portfolioConfig.debugConfig,
  )

fun XcfaConfig<*, AsgCegarConfig>.adaptConfig(
  initPrec: InitPrec = this.backendConfig.specConfig!!.initPrec,
  timeoutMs: Long = this.backendConfig.timeoutMs,
  domain: Domain = this.backendConfig.specConfig!!.abstractorConfig.domain,
  refinement: ASGTraceCheckerStrategy = this.backendConfig.specConfig!!.refinerConfig.refinement,
  exprSplitter: ExprSplitterOptions = this.backendConfig.specConfig!!.refinerConfig.exprSplitter,
  abstractionSolver: String = this.backendConfig.specConfig!!.abstractorConfig.abstractionSolver,
  validateAbstractionSolver: Boolean =
    this.backendConfig.specConfig!!.abstractorConfig.validateAbstractionSolver,
  refinementSolver: String = this.backendConfig.specConfig!!.refinerConfig.refinementSolver,
  validateRefinementSolver: Boolean =
    this.backendConfig.specConfig!!.refinerConfig.validateRefinementSolver,
  inProcess: Boolean = this.backendConfig.inProcess,
): XcfaConfig<*, AsgCegarConfig> {
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
                  exprSplitter = exprSplitter,
                ),
          ),
      )
  )
}

fun baseBoundedConfig(portfolioConfig: XcfaConfig<*, *>): XcfaConfig<*, BoundedConfig> =
  XcfaConfig(
    inputConfig = portfolioConfig.inputConfig,
    frontendConfig = portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>,
    backendConfig =
      BackendConfig(
        backend = Backend.BOUNDED,
        memlimit = portfolioConfig.backendConfig.memlimit,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        specConfig =
          BoundedConfig(
            bmcConfig = BMCConfig(true),
            maxBound = 0,
            indConfig = InductionConfig(true),
            itpConfig = InterpolationConfig(true),
          ),
      ),
    outputConfig = getDefaultOutputConfig(portfolioConfig),
    debugConfig = portfolioConfig.debugConfig,
  )

fun baseMddConfig(portfolioConfig: XcfaConfig<*, *>): XcfaConfig<*, MddConfig> =
  XcfaConfig(
    inputConfig = portfolioConfig.inputConfig,
    frontendConfig = portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>,
    backendConfig =
      BackendConfig(
        backend = Backend.MDD,
        memlimit = portfolioConfig.backendConfig.memlimit / 5 * 4,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        specConfig =
          MddConfig(
            solver = "Z3",
            validateSolver = false,
            iterationStrategy = IterationStrategy.GSAT,
            reversed = false,
            cegar = false,
            initPrec = EMPTY,
          ),
      ),
    outputConfig = getDefaultOutputConfig(portfolioConfig),
    debugConfig = portfolioConfig.debugConfig,
  )

fun XcfaConfig<*, BoundedConfig>.adaptConfig(
  bmcEnabled: Boolean = false,
  indEnabled: Boolean = false,
  itpEnabled: Boolean = false,
  bmcSolver: String = "Z3",
  indSolver: String = "Z3",
  itpSolver: String = solverVersionOrLatestFallback("cvc5", "1.0.8"),
  timeoutMs: Long = 0,
  inProcess: Boolean = this.backendConfig.inProcess,
  reversed: Boolean = false,
  cegar: Boolean = false,
  initprec: InitPrec = EMPTY,
): XcfaConfig<*, BoundedConfig> =
  copy(
    backendConfig =
      backendConfig.copy(
        timeoutMs = timeoutMs,
        inProcess = inProcess,
        specConfig =
          backendConfig.specConfig!!.copy(
            reversed = reversed,
            cegar = cegar,
            initPrec = initprec,
            bmcConfig =
              backendConfig.specConfig!!
                .bmcConfig
                .copy(disable = !bmcEnabled, bmcSolver = bmcSolver),
            indConfig =
              backendConfig.specConfig!!
                .indConfig
                .copy(disable = !indEnabled, indSolver = indSolver),
            itpConfig =
              backendConfig.specConfig!!
                .itpConfig
                .copy(disable = !itpEnabled, itpSolver = itpSolver),
          ),
      )
  )

fun baseIc3Config(portfolioConfig: XcfaConfig<*, *>): XcfaConfig<*, Ic3Config> =
  XcfaConfig(
    inputConfig = portfolioConfig.inputConfig,
    frontendConfig = portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>,
    backendConfig =
      BackendConfig(
        backend = Backend.IC3,
        memlimit = portfolioConfig.backendConfig.memlimit,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        specConfig =
          Ic3Config(solver = "Z3", validateSolver = false, reversed = false, cegar = true),
      ),
    outputConfig = getDefaultOutputConfig(portfolioConfig),
    debugConfig = portfolioConfig.debugConfig,
  )

fun getDefaultOutputConfig(portfolioConfig: XcfaConfig<*, *>) =
  OutputConfig(
    enabled = portfolioConfig.outputConfig.enabled,
    resultFolder = portfolioConfig.outputConfig.resultFolder, // cwd
    acceptUnreliableSafe = portfolioConfig.outputConfig.acceptUnreliableSafe,
    cOutputConfig = portfolioConfig.outputConfig.cOutputConfig,
    xcfaOutputConfig = portfolioConfig.outputConfig.xcfaOutputConfig,
    chcOutputConfig = portfolioConfig.outputConfig.chcOutputConfig,
    witnessConfig =
      WitnessConfig(
        enabled = portfolioConfig.outputConfig.witnessConfig.enabled,
        concretizerSolver = portfolioConfig.outputConfig.witnessConfig.concretizerSolver,
        validateConcretizerSolver = portfolioConfig.outputConfig.witnessConfig.validateConcretizerSolver,
        inputFileForWitness =
          portfolioConfig.outputConfig.witnessConfig.inputFileForWitness
            ?: portfolioConfig.inputConfig.input,
      ),
    argConfig = portfolioConfig.outputConfig.argConfig,
  )
