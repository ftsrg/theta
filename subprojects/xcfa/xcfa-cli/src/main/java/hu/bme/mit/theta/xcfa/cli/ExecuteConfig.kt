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
package hu.bme.mit.theta.xcfa.cli

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.*
import hu.bme.mit.theta.analysis.algorithm.arg.debug.ARGWebDebugger
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSet
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.TraceGenerationResult
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.cat.dsl.CatDslManager
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.INFO
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.UnknownResultException
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.ltlPropertyFromTrace
import hu.bme.mit.theta.xcfa.analysis.oc.OcDecisionProcedureType
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.analysis.por.XcfaSporLts
import hu.bme.mit.theta.xcfa.cli.checkers.getChecker
import hu.bme.mit.theta.xcfa.cli.checkers.getSafetyChecker
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.OutputLevel.NONE
import hu.bme.mit.theta.xcfa.cli.utils.*
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.ApplyWitnessPassesManager
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.isDataRacePossible
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import java.util.concurrent.TimeUnit
import kotlin.random.Random
import kotlin.system.exitProcess
import kotlinx.serialization.builtins.ListSerializer

fun runConfig(
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
  throwDontExit: Boolean,
): Result<*> {
  propagateInputOptions(config, logger, uniqueLogger)

  registerAllSolverManagers(config.backendConfig.solverHome, logger)

  val (xcfa, mcm, parseContext) =
    parseInputFiles(config, logger, uniqueLogger) // this handles pre-analysis logging as well

  validateInputOptions(config, logger, uniqueLogger)

  val result = backend(xcfa, mcm, parseContext, config, logger, uniqueLogger, throwDontExit)

  postAnalysisLogging(xcfa, result, mcm, parseContext, config, logger, uniqueLogger)

  return result
}

private fun propagateInputOptions(config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger) {
  config.inputConfig.property = determineProperty(config, logger)
  LbePass.defaultLevel = config.frontendConfig.lbeLevel
  StaticCoiPass.enabled = config.frontendConfig.enableStaticCoi
  DataRaceToReachabilityPass.enabled = config.frontendConfig.enableDataRaceToReachability

  if (config.backendConfig.backend == Backend.CEGAR) {
    val cegarConfig = config.backendConfig.specConfig
    cegarConfig as CegarConfig
    val random = Random(cegarConfig.porSeed)
    XcfaSporLts.random = random
    XcfaDporLts.random = random
  }
  if (config.inputConfig.property.inputProperty == ErrorDetection.TERMINATION) {
    RemoveDeadEnds.enabled = false
  }
  if (
    config.inputConfig.property.inputProperty == ErrorDetection.MEMSAFETY ||
      config.inputConfig.property.inputProperty == ErrorDetection.MEMCLEANUP
  ) {
    MemsafetyPass.enabled = true
  }
  if (config.inputConfig.property.inputProperty == ErrorDetection.DATA_RACE) {
    StaticCoiPass.enabled = false
    UnusedVarPass.keepGlobalVariableAccesses = true
  }
  if (config.debugConfig.argToFile) {
    WebDebuggerLogger.enableWebDebuggerLogger()
    WebDebuggerLogger.getInstance().setTitle(config.inputConfig.input?.name)
  }

  LoopUnrollPass.UNROLL_LIMIT = config.frontendConfig.loopUnroll
  LoopUnrollPass.FORCE_UNROLL_LIMIT = config.frontendConfig.forceUnroll
  FetchExecuteWriteback.enabled = config.frontendConfig.enableFew
  ARGWebDebugger.on = config.debugConfig.argdebug
}

private fun validateInputOptions(config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger) {
  rule("NoLbeFullWhenCegar") {
    config.backendConfig.backend == Backend.CEGAR &&
      (config.frontendConfig.lbeLevel == LbePass.LbeLevel.LBE_FULL ||
        config.frontendConfig.lbeLevel == LbePass.LbeLevel.LBE_LOCAL_FULL)
  }
  rule("NoCoiWhenDataRace") {
    config.backendConfig.backend == Backend.CEGAR &&
      (config.backendConfig.specConfig as? CegarConfig)?.coi != ConeOfInfluenceMode.NO_COI &&
      config.inputConfig.property.verifiedProperty == ErrorDetection.DATA_RACE
  }
  rule("NoAaporWhenDataRace") {
    (config.backendConfig.specConfig as? CegarConfig)?.por?.isAbstractionAware == true &&
      config.inputConfig.property.verifiedProperty == ErrorDetection.DATA_RACE
  }
  rule("DPORWithoutDFS") {
    (config.backendConfig.specConfig as? CegarConfig)?.por?.isDynamic == true &&
      (config.backendConfig.specConfig as? CegarConfig)?.abstractorConfig?.search != Search.DFS
  }
  rule("SensibleLoopUnrollLimits") {
    config.frontendConfig.loopUnroll != -1 &&
      config.frontendConfig.loopUnroll < config.frontendConfig.forceUnroll
  }
  rule("NoPredSplitUntilFixed(https://github.com/ftsrg/theta/issues/267)") {
    (config.backendConfig.specConfig as? CegarConfig)?.abstractorConfig?.domain == Domain.PRED_SPLIT
  }
  rule("OcPropagatorWithoutZ3") {
    config.backendConfig.backend == Backend.OC &&
      (config.backendConfig.specConfig as? OcConfig)?.decisionProcedure ==
        OcDecisionProcedureType.PROPAGATOR &&
      (config.backendConfig.specConfig as? OcConfig)?.smtSolver != "Z3:new"
  }
  rule("SensibleOutputOptions", false) {
    config.outputConfig.enabled == NONE &&
      (config.outputConfig.xcfaOutputConfig.enabled ||
        config.outputConfig.cOutputConfig.enabled ||
        config.outputConfig.chcOutputConfig.enabled ||
        config.outputConfig.argConfig.enabled ||
        config.outputConfig.witnessConfig.enabled != WitnessLevel.NONE)
  }
}

private fun parseInputFiles(
  config: XcfaConfig<*, *>, logger: Logger,
  uniqueLogger: Logger
): Triple<XCFA?, MCM?, ParseContext?> = if (config.backendConfig.inProcess && config.backendConfig.parseInProcess) {
  logger.info("Not parsing input because a worker process will handle it later.")
  Triple(null, null, null)
} else {
  var (xcfa, mcm, parseContext) = frontend(config, logger, uniqueLogger)

  applyOptionalWitness(config, logger, xcfa, parseContext)

  preAnalysisLogging(xcfa, mcm, parseContext, config, logger, uniqueLogger)
  Triple(xcfa, mcm, parseContext)
}

private fun applyOptionalWitness(
  config: XcfaConfig<*, *>, logger: Logger,
  xcfa: XCFA, parseContext: ParseContext
): XCFA {
  return config.inputConfig.witness?.let {
    logger.info("Applying witness $it")
    if (!it.exists()) {
      exitProcess(ExitCodes.INVALID_PARAM.code)
    }
    val witness =
      WitnessYamlConfig.decodeFromString(
        ListSerializer(YamlWitness.serializer()),
        it.readText(),
      )[0]
    xcfa.optimizeFurther(ApplyWitnessPassesManager(parseContext, witness))
  } ?: xcfa
}

private fun frontend(
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): Triple<XCFA, MCM, ParseContext> {
  if (config.inputConfig.xcfaWCtx != null) {
    return config.inputConfig.xcfaWCtx!!
  }

  val stopwatch = Stopwatch.createStarted()

  val input = config.inputConfig.input!!
  logger.info("Parsing the input $input as ${config.frontendConfig.inputType}")

  val parseContext = ParseContext()

  if (config.frontendConfig.inputType == InputType.C) {
    val cConfig = config.frontendConfig.specConfig
    cConfig as CFrontendConfig
    parseContext.arithmetic = cConfig.arithmetic
    parseContext.architecture = cConfig.architecture
  }

  val xcfa = getXcfa(config, parseContext, logger, uniqueLogger)
  val mcm =
    if (config.inputConfig.catFile != null) {
      CatDslManager.createMCM(config.inputConfig.catFile!!)
    } else {
      emptySet()
    }

  if (
    parseContext.multiThreading &&
      (config.backendConfig.specConfig as? CegarConfig)?.let {
        it.abstractorConfig.search == Search.ERR
      } == true
  ) {
    val cConfig = config.backendConfig.specConfig as CegarConfig
    cConfig.abstractorConfig.search = Search.DFS
    uniqueLogger.write(INFO, "Multithreaded program found, using DFS instead of ERR.")
  }

  logger.info(
    "Frontend finished: ${xcfa.name}  (in ${stopwatch.elapsed(TimeUnit.MILLISECONDS)} ms)"
  )

  logger.result("ParsingResult Success")
  logger.info(
    "Alias graph size: ${xcfa.pointsToGraph.size} -> ${xcfa.pointsToGraph.values.map { it.size }.toList()}"
  )

  return Triple(xcfa, mcm, parseContext)
}

private fun backend(
  xcfa: XCFA?,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
  throwDontExit: Boolean,
): Result<*> =
  if (config.backendConfig.backend == Backend.NONE) {
    SafetyResult.unknown<EmptyProof, EmptyCex>()
  } else if (config.backendConfig.backend == Backend.TRACEGEN) {
    tracegenBackend(xcfa, mcm, parseContext, config, logger, uniqueLogger, throwDontExit)
  } else {
    if (
      config.inputConfig.property.verifiedProperty == ErrorDetection.ERROR_LOCATION &&
        (xcfa?.procedures?.all { it.errorLoc.isEmpty } ?: false)
    ) {
      val result = SafetyResult.safe<EmptyProof, EmptyCex>(EmptyProof.getInstance())
      logger.result("Input is trivially safe")
      logger.result(result.toString())
      result
    } else if (
      config.inputConfig.property.verifiedProperty == ErrorDetection.DATA_RACE &&
        xcfa != null &&
        !isDataRacePossible(xcfa, logger)
    ) {
      val result = SafetyResult.safe<EmptyProof, EmptyCex>(EmptyProof.getInstance())
      logger.result(
        "Input is trivially safe: potential concurrent accesses to the same memory locations are either all atomic or all read accesses."
      )
      logger.result(result.toString())
      result
    } else {
      val stopwatch = Stopwatch.createStarted()

      logger.info(
        "Input/Verified property: ${config.inputConfig.property.inputProperty.name} / ${config.inputConfig.property.verifiedProperty.name}"
      )

      logger.info(
        "Starting verification of ${if (xcfa?.name == "") "UnnamedXcfa" else (xcfa?.name ?: "DeferredXcfa")} using ${config.backendConfig.backend}\n${config}"
      )

      val checker = getSafetyChecker(xcfa, mcm, config, parseContext, logger, uniqueLogger)
      val result =
        exitOnError(config.debugConfig.stacktrace, config.debugConfig.debug || throwDontExit) {
            checker.check()
          }
          .let ResultMapper@{ result ->
            result as SafetyResult<*, *>
            when {
              result.isSafe && xcfa?.unsafeUnrollUsed ?: false -> {
                // cannot report safe if force unroll was used
                logger.result("Incomplete loop unroll used: safe result is unreliable.")
                if (config.outputConfig.acceptUnreliableSafe)
                  result // for comparison with BMC tools
                else SafetyResult.unknown<EmptyProof, EmptyCex>()
              }

              result.isUnsafe -> {
                // need to determine what kind
                val property =
                  try {
                    config.inputConfig.property.ltlPropertyFromTrace(
                      result.asUnsafe().cex as? Trace<XcfaState<*>, XcfaAction>
                    )
                  } catch (e: UnknownResultException) {
                    return@ResultMapper SafetyResult.unknown<EmptyProof, EmptyCex>()
                  }
                property?.also { logger.result("(Property %s)", it) }
                result
              }

              else -> {
                result
              }
            }
          }

      logger.info("Backend finished (in ${stopwatch.elapsed(TimeUnit.MILLISECONDS)} ms)")
      logger.result(result.toString())
      result
    }
  }

private fun tracegenBackend(
  xcfa: XCFA?,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
  throwDontExit: Boolean,
): Result<*> {
  val stopwatch = Stopwatch.createStarted()
  val checker =
    getChecker(xcfa, mcm, config, parseContext, logger, uniqueLogger)
      as Checker<AbstractTraceSummary<XcfaState<*>, XcfaAction>, XcfaPrec<*>>
  val result =
    exitOnError(config.debugConfig.stacktrace, config.debugConfig.debug || throwDontExit) {
      checker.check(XcfaPrec(PtrPrec(ExplPrec.of(xcfa!!.collectVars()), emptySet())))
    }
  logger.info(
    "Backend finished (in ${
      stopwatch.elapsed(TimeUnit.MILLISECONDS)
    } ms)\n",
  )

  return result
}

private fun postAnalysisLogging(
  xcfa: XCFA?,
  result: Result<*>,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) =
  when (config.backendConfig.backend) {
    Backend.TRACEGEN ->
      postTraceGenerationLogging(
        result
          as
          TraceGenerationResult<
            AbstractTraceSet<XcfaState<*>, XcfaAction>,
            XcfaState<*>,
            XcfaAction,
          >,
        mcm,
        parseContext,
        config,
        logger,
        uniqueLogger,
      )
    else ->
      postVerificationLogging(
        xcfa,
        result as SafetyResult<*, *>,
        mcm,
        parseContext,
        config,
        logger,
        uniqueLogger,
      ) // safety analysis (or none)
  }

internal fun concretizeTrace(
  trace: Cex?, config: XcfaConfig<*, *>,
  parseContext: ParseContext
): Trace<XcfaState<ExplState>, XcfaAction> = XcfaTraceConcretizer.concretize(
  trace as Trace<XcfaState<PtrState<*>>, XcfaAction>,
  getSolver(
    config.outputConfig.witnessConfig.concretizerSolver,
    config.outputConfig.witnessConfig.validateConcretizerSolver,
  ),
  parseContext,
)