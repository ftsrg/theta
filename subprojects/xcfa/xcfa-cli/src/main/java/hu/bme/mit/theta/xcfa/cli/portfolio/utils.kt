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

import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopCheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.FULL
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy.LAZY
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType.efficient
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
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
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass

fun baseCegarConfig(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  serialize: Boolean,
): XcfaConfig<*, CegarConfig> {
  var baseConfig =
    XcfaConfig(
      inputConfig =
        if (serialize)
          portfolioConfig.inputConfig.copy(
            xcfaWCtx =
              if (portfolioConfig.backendConfig.parseInProcess) null
              else Triple(xcfa, mcm, parseContext),
            propertyFile = null,
            property = portfolioConfig.inputConfig.property,
          )
        else portfolioConfig.inputConfig,
      frontendConfig =
        if (serialize)
          FrontendConfig(
            lbeLevel = LbePass.defaultLevel,
            loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
            inputType = InputType.C,
            specConfig = CFrontendConfig(arithmetic = efficient),
          )
        else (portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>),
      backendConfig =
        BackendConfig(
          backend = CEGAR,
          solverHome = portfolioConfig.backendConfig.solverHome,
          timeoutMs = 0,
          parseInProcess = !serialize,
          specConfig =
            CegarConfig(
              initPrec = EMPTY,
              por = NOPOR,
              porSeed = -1,
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
  inProcess: Boolean = this.backendConfig.inProcess,
): XcfaConfig<*, CegarConfig> {
  return copy(
    backendConfig =
      backendConfig.copy(
        timeoutMs = timeoutMs,
        inProcess = inProcess,
        parseInProcess = inProcess && this.backendConfig.parseInProcess,
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
            coi = coi,
          ),
      )
  )
}

fun baseAsgCegarConfig(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  serialize: Boolean,
): XcfaConfig<SpecFrontendConfig, AsgCegarConfig> =
  XcfaConfig(
    inputConfig =
      if (serialize)
        portfolioConfig.inputConfig.copy(
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        )
      else portfolioConfig.inputConfig,
    frontendConfig =
      if (serialize)
        FrontendConfig(
          lbeLevel = LbePass.defaultLevel,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = efficient),
        )
      else (portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>),
    backendConfig =
      BackendConfig(
        backend = Backend.LIVENESS_CEGAR,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        parseInProcess = !serialize,
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
        parseInProcess = inProcess && backendConfig.parseInProcess,
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

fun baseBoundedConfig(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  serialize: Boolean,
): XcfaConfig<*, BoundedConfig> =
  XcfaConfig(
    inputConfig =
      if (serialize)
        portfolioConfig.inputConfig.copy(
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        )
      else portfolioConfig.inputConfig,
    frontendConfig =
      if (serialize)
        FrontendConfig(
          lbeLevel = LbePass.defaultLevel,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = efficient),
        )
      else (portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>),
    backendConfig =
      BackendConfig(
        backend = Backend.BOUNDED,
        memlimit = portfolioConfig.backendConfig.memlimit,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        parseInProcess = !serialize,
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

fun baseMddConfig(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  serialize: Boolean,
): XcfaConfig<*, MddConfig> =
  XcfaConfig(
    inputConfig =
      if (serialize)
        portfolioConfig.inputConfig.copy(
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        )
      else portfolioConfig.inputConfig,
    frontendConfig =
      if (serialize)
        FrontendConfig(
          lbeLevel = LbePass.defaultLevel,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = efficient),
        )
      else (portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>),
    backendConfig =
      BackendConfig(
        backend = Backend.MDD,
        memlimit = portfolioConfig.backendConfig.memlimit / 5 * 4,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        parseInProcess = !serialize,
        specConfig =
          MddConfig(
            solver = "Z3",
            validateSolver = false,
            iterationStrategy = MddChecker.IterationStrategy.GSAT,
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
  itpSolver: String = "cvc5:1.0.8",
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
        parseInProcess = inProcess && backendConfig.parseInProcess,
      )
  )

fun baseIc3Config(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  portfolioConfig: XcfaConfig<*, *>,
  serialize: Boolean,
): XcfaConfig<*, Ic3Config> =
  XcfaConfig(
    inputConfig =
      if (serialize)
        portfolioConfig.inputConfig.copy(
          xcfaWCtx = Triple(xcfa, mcm, parseContext),
          propertyFile = null,
          property = portfolioConfig.inputConfig.property,
        )
      else portfolioConfig.inputConfig,
    frontendConfig =
      if (serialize)
        FrontendConfig(
          lbeLevel = LbePass.defaultLevel,
          loopUnroll = LoopUnrollPass.UNROLL_LIMIT,
          inputType = InputType.C,
          specConfig = CFrontendConfig(arithmetic = efficient),
        )
      else (portfolioConfig.frontendConfig as FrontendConfig<SpecFrontendConfig>),
    backendConfig =
      BackendConfig(
        backend = Backend.IC3,
        memlimit = portfolioConfig.backendConfig.memlimit,
        solverHome = portfolioConfig.backendConfig.solverHome,
        timeoutMs = 0,
        parseInProcess = !serialize,
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
        enabled = WitnessLevel.SVCOMP,
        concretizerSolver = "Z3",
        validateConcretizerSolver = false,
        inputFileForWitness =
          portfolioConfig.outputConfig.witnessConfig.inputFileForWitness
            ?: portfolioConfig.inputConfig.input,
      ),
    argConfig = portfolioConfig.outputConfig.argConfig,
  )
