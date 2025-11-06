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
import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.*
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.debug.ARGWebDebugger
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.asg.HackyAsgTrace
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSet
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.TraceGenerationResult
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.cat.dsl.CatDslManager
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.INFO
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
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
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isDataRacePossible
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import hu.bme.mit.theta.xcfa2chc.RankingFunction
import hu.bme.mit.theta.xcfa2chc.toSMT2CHC
import java.io.File
import java.io.PrintWriter
import java.util.concurrent.TimeUnit
import kotlin.random.Random
import kotlin.system.exitProcess
import kotlinx.serialization.builtins.ListSerializer
import org.mockito.kotlin.lt

fun runConfig(
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
  throwDontExit: Boolean,
): Result<*> {
  propagateInputOptions(config, logger, uniqueLogger)

  registerAllSolverManagers(config.backendConfig.solverHome, logger)

  val (xcfa, mcm, parseContext) =
    if (config.backendConfig.inProcess && config.backendConfig.parseInProcess) {
      logger.info("Not parsing input because a worker process will handle it later.")
      Triple(null, null, null)
    } else {
      var (xcfa, mcm, parseContext) = frontend(config, logger, uniqueLogger)

      config.inputConfig.witness?.also {
        logger.writeln(INFO, "Applying witness $it")
        if (!it.exists()) {
          exitProcess(ExitCodes.INVALID_PARAM.code)
        }
        val witness =
          WitnessYamlConfig.decodeFromString(
            ListSerializer(YamlWitness.serializer()),
            it.readText(),
          )[0]
        xcfa = xcfa.optimizeFurther(ApplyWitnessPassesManager(parseContext, witness))
      }

      preAnalysisLogging(xcfa, mcm, parseContext, config, logger, uniqueLogger)
      Triple(xcfa, mcm, parseContext)
    }

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

fun frontend(
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
  if (config.backendConfig.backend == Backend.TRACEGEN) {
    tracegenBackend(xcfa, mcm, parseContext, config, logger, uniqueLogger, throwDontExit)
  } else if (config.backendConfig.backend == Backend.NONE) {
    SafetyResult.unknown<EmptyProof, EmptyCex>()
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
  logger.write(
    Logger.Level.INFO,
    "Backend finished (in ${
      stopwatch.elapsed(TimeUnit.MILLISECONDS)
    } ms)\n",
  )

  return result
}

private fun preAnalysisLogging(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) {
  if (config.outputConfig.enabled != NONE) {
    try {
      val enabled = config.outputConfig.enabled == OutputLevel.ALL
      val resultFolder = config.outputConfig.resultFolder
      resultFolder.mkdirs()

      logger.info(
        "Writing pre-verification artifacts to directory ${resultFolder.absolutePath} with config ${config.outputConfig}"
      )

      if (enabled || config.outputConfig.chcOutputConfig.enabled) {
        xcfa.procedures.forEach {
          try {
            val chcFile = File(resultFolder, "xcfa-${it.name}.smt2")
            chcFile.writeText(
              it.toSMT2CHC(
                config.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION,
                (config.backendConfig.specConfig as? HornConfig)?.rankingFuncConstr
                  ?: RankingFunction.ADD,
              )
            )
          } catch (e: Exception) {
            logger.info("Could not emit XCFA as CHC file: ${e.stackTraceToString()}")
          }
        }
      }

      if (enabled || config.outputConfig.xcfaOutputConfig.enabled) {
        try {
          val xcfaDotFile = File(resultFolder, "xcfa.dot")
          xcfaDotFile.writeText(xcfa.toDot())
        } catch (e: Exception) {
          logger.info("Could not emit XCFA as DOT file: ${e.stackTraceToString()}")
        }

        try {
          val xcfaJsonFile = File(resultFolder, "xcfa.json")
          val uglyJson = getGson(xcfa).toJson(xcfa)
          val create = GsonBuilder().setPrettyPrinting().create()
          xcfaJsonFile.writeText(create.toJson(JsonParser.parseString(uglyJson)))
        } catch (e: Exception) {
          logger.info("Could not emit XCFA as JSON file: ${e.stackTraceToString()}")
        }
      }

      if (enabled || config.outputConfig.cOutputConfig.enabled) {
        try {
          val xcfaCFile = File(resultFolder, "xcfa.c")
          xcfaCFile.writeText(
            xcfa.toC(
              parseContext,
              config.outputConfig.cOutputConfig.useArr,
              config.outputConfig.cOutputConfig.useExArr,
              config.outputConfig.cOutputConfig.useRange,
            )
          )
        } catch (e: Throwable) {
          logger.info("Could not emit XCFA as C file: ${e.stackTraceToString()}")
        }
      }
    } catch (e: Throwable) {
      logger.info("Could not output files: ${e.stackTraceToString()}")
    }
  }
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

private fun postVerificationLogging(
  xcfa: XCFA?,
  safetyResult: SafetyResult<*, *>,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) {
  val forceEnabledOutput = config.outputConfig.enabled == OutputLevel.ALL
  if (
    config.frontendConfig.inputType == InputType.CHC &&
      xcfa != null &&
      ((config.frontendConfig.specConfig as CHCFrontendConfig).model || forceEnabledOutput)
  ) {
    val resultFolder = config.outputConfig.resultFolder
    resultFolder.mkdirs()
    val chcAnswer = writeModel(xcfa, safetyResult)
    val chcAnswerFile = File(resultFolder, "chc-answer.smt2")
    if (chcAnswerFile.exists()) {
      logger.info("CHC answer/model already written to file $chcAnswerFile, not overwriting")
    } else {
      chcAnswerFile.writeText(chcAnswer)
      logger.info("CHC answer/model written to file $chcAnswerFile")
    }
  }

  // we only want to log the files if the current configuration is not --in-process or portfolio
  if (config.backendConfig.inProcess || config.backendConfig.backend == Backend.PORTFOLIO) {
    return
  }

  if (config.outputConfig.enabled != NONE && mcm != null && parseContext != null) {
    try {
      val resultFolder = config.outputConfig.resultFolder
      resultFolder.mkdirs()
      logger.info("Writing post-verification artifacts to directory ${resultFolder.absolutePath}")

      // TODO eliminate the need for the instanceof check
      if (
        (forceEnabledOutput || config.outputConfig.argConfig.enabled) &&
          safetyResult.proof is ARG<out State, out Action>
      ) {
        try {
          val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
          val g: Graph =
            ArgVisualizer.getDefault().visualize(safetyResult.proof as ARG<out State, out Action>)
          argFile.writeText(GraphvizWriter.getInstance().writeString(g))
        } catch (e: Exception) {
          logger.info("Could not emit ARG as DOT file: ${e.stackTraceToString()}")
        }
      }

      when {
        config.outputConfig.witnessConfig.enabled == WitnessLevel.SVCOMP -> {
          try {
            val witnessWriter =
              XcfaWitnessWriter.getSvCompWitnessWriter(
                config.inputConfig.property,
                parseContext,
                safetyResult,
              )

            if (witnessWriter != null) {
              val witnessFile = File(resultFolder, "witness.${witnessWriter.extension}")
              witnessWriter.writeWitness(
                safetyResult,
                config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
                config.inputConfig.property,
                getSolver(
                  config.outputConfig.witnessConfig.concretizerSolver,
                  config.outputConfig.witnessConfig.validateConcretizerSolver,
                ),
                parseContext,
                witnessFile,
                (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture,
              )
            } else {
              logger.info(
                "No suitable SV-COMP witness writer found for the given property (${config.inputConfig.property.inputProperty}), category (${if (parseContext.multiThreading) "concurrency" else "not concurrency"}) and safety result ($safetyResult)."
              )
            }
          } catch (e: Exception) {
            logger.info(
              "Could not emit witness in the required SV-COMP format: ${e.stackTraceToString()}"
            )
          }
        }

        forceEnabledOutput || config.outputConfig.witnessConfig.enabled == WitnessLevel.ALL -> {
          if (safetyResult.isUnsafe && safetyResult.asUnsafe().cex != null) {
            val trace =
              if (safetyResult.asUnsafe().cex is HackyAsgTrace<*>) {
                val actions = (safetyResult.asUnsafe().cex as HackyAsgTrace<*>).trace.actions
                val explStates = (safetyResult.asUnsafe().cex as HackyAsgTrace<*>).trace.states
                val states =
                  (safetyResult.asUnsafe().cex as HackyAsgTrace<*>).originalStates.mapIndexed {
                      i,
                      state ->
                    state as XcfaState<PtrState<*>>
                    state.withState(PtrState(explStates[i]))
                  }

                Trace.of(states, actions)
              } else if (safetyResult.asUnsafe().cex is ASGTrace<*, *>) {
                (safetyResult.asUnsafe().cex as ASGTrace<*, *>).toTrace()
              } else {
                safetyResult.asUnsafe().cex
              }
            val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
              XcfaTraceConcretizer.concretize(
                trace as Trace<XcfaState<PtrState<*>>, XcfaAction>,
                getSolver(
                  config.outputConfig.witnessConfig.concretizerSolver,
                  config.outputConfig.witnessConfig.validateConcretizerSolver,
                ),
                parseContext,
              )

            try {
              val traceFile = File(resultFolder, "trace.dot")
              val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
              traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
            } catch (e: Exception) {
              logger.info("Could not emit trace as DOT file: ${e.stackTraceToString()}")
            }

            try {
              val sequenceFile = File(resultFolder, "trace.plantuml")
              writeSequenceTrace(
                sequenceFile,
                trace as Trace<XcfaState<ExplState>, XcfaAction>,
              ) { (_, act) ->
                act.label.getFlatLabels().map(XcfaLabel::toString)
              }
            } catch (e: Exception) {
              logger.info("Could not emit trace as PlantUML file: ${e.stackTraceToString()}")
            }

            try {
              val optSequenceFile = File(resultFolder, "trace-optimized.plantuml")
              writeSequenceTrace(optSequenceFile, concrTrace) { (_, act) ->
                act.label.getFlatLabels().map(XcfaLabel::toString)
              }
            } catch (e: Exception) {
              logger.info(
                "Could not emit optimized trace as PlantUML file: ${e.stackTraceToString()}"
              )
            }

            try {
              val cSequenceFile = File(resultFolder, "trace-c.plantuml")
              writeSequenceTrace(cSequenceFile, concrTrace) { (state, act) ->
                val proc = state.processes[act.pid]
                val loc = proc?.locs?.peek()
                (loc?.metadata as? CMetaData)?.sourceText?.split("\n") ?: listOf("<unknown>")
              }
            } catch (e: Exception) {
              logger.info("Could not emit C trace as PlantUML file: ${e.stackTraceToString()}")
            }
          }

          val ltlViolationProperty =
            if (safetyResult.isUnsafe) {
              config.inputConfig.property.ltlPropertyFromTrace(
                safetyResult.asUnsafe().cex as? Trace<XcfaState<*>, XcfaAction>
              )!!
            } else null

          try {
            val witnessFile = File(resultFolder, "witness.graphml")
            GraphmlWitnessWriter()
              .writeWitness(
                safetyResult,
                config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
                config.inputConfig.property,
                getSolver(
                  config.outputConfig.witnessConfig.concretizerSolver,
                  config.outputConfig.witnessConfig.validateConcretizerSolver,
                ),
                parseContext,
                witnessFile,
                ltlViolationProperty
              )
          } catch (e: Exception) {
            logger.info("Could not emit witness as GraphML file: ${e.stackTraceToString()}")
          }

          try {
            val yamlWitnessFile = File(resultFolder, "witness.yml")
            YamlWitnessWriter()
              .writeWitness(
                safetyResult,
                config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
                config.inputConfig.property,
                getSolver(
                  config.outputConfig.witnessConfig.concretizerSolver,
                  config.outputConfig.witnessConfig.validateConcretizerSolver,
                ),
                parseContext,
                yamlWitnessFile,
                (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture,
                ltlViolationProperty
              )
          } catch (e: Exception) {
            logger.info("Could not emit witness as YAML file: ${e.stackTraceToString()}")
          }
        }

        else -> {}
      }
    } catch (e: Throwable) {
      logger.info("Could not output files: ${e.stackTraceToString()}")
    }
  }
}

private fun writeSequenceTrace(
  sequenceFile: File,
  trace: Trace<XcfaState<ExplState>, XcfaAction>,
  printer: (Pair<XcfaState<ExplState>, XcfaAction>) -> List<String>,
) {
  sequenceFile.writeText("@startuml\n")
  var maxWidth = 0
  trace.actions.forEachIndexed { i, it ->
    val stateBefore = trace.states[i]
    sequenceFile.appendText("hnote over ${it.pid}\n")
    val labelStrings = printer(Pair(stateBefore, it))
    if (maxWidth < (labelStrings.maxOfOrNull { it.length } ?: 0)) {
      maxWidth = labelStrings.maxOfOrNull { it.length } ?: 0
    }
    sequenceFile.appendText("${labelStrings.joinToString("\n")}\n")
    sequenceFile.appendText("endhnote\n")
  }
  trace.actions
    .map { it.pid }
    .distinct()
    .reduce { acc, current ->
      sequenceFile.appendText("$acc --> $current: \"${" ".repeat(maxWidth)}\"\n")
      current
    }
  sequenceFile.appendText("@enduml\n")
}

private fun postTraceGenerationLogging(
  result:
    TraceGenerationResult<AbstractTraceSet<XcfaState<*>, XcfaAction>, XcfaState<*>, XcfaAction>,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) {
  /*
  val abstractSummary = result.summary
  logger.write(
    Logger.Level.MAINSTEP,
    "Successfully generated a summary of ${abstractSummary.sourceTraces.size} abstract traces.\n",
  )
   */

  val resultFolder = config.outputConfig.resultFolder
  resultFolder.mkdirs()

  if (config.outputConfig.enableOutput) {
    logger.write(
      Logger.Level.MAINSTEP,
      "Writing post-verification artifacts to directory ${resultFolder.absolutePath}\n",
    )
    val modelName = config.inputConfig.input!!.name
    /*
        val graph = AbstractTraceSummaryVisualizer.visualize(abstractSummary)
        val visFile =
          resultFolder.absolutePath + File.separator + modelName + ".abstract-trace-summary.png"
        GraphvizWriter.getInstance().writeFileAutoConvert(graph, visFile)
        logger.write(Logger.Level.SUBSTEP, "Abstract trace summary was visualized in ${visFile}\n")
    */
    var concreteTraces = 1
    for (abstractTrace in result.summary.sourceTraces) {
      try {
        // TODO no concrete summary implemented for XCFA yet, only traces
        val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
          XcfaTraceConcretizer.concretize(
            abstractTrace.toTrace() as Trace<XcfaState<PtrState<*>>, XcfaAction>,
            getSolver(
              config.outputConfig.witnessConfig.concretizerSolver,
              config.outputConfig.witnessConfig.validateConcretizerSolver,
            ),
            parseContext,
          )

        val concreteTraceFile =
          resultFolder.absolutePath + File.separator + modelName + "_${concreteTraces}.cex"

        PrintWriter(File(concreteTraceFile)).use { printWriter ->
          printWriter.write(concrTrace.toString())
        }

        val concreteDotFile =
          File(resultFolder.absolutePath + File.separator + modelName + "_${concreteTraces}.dot")
        val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
        concreteDotFile.writeText(GraphvizWriter.getInstance().writeString(traceG))

        val yamlWitnessFile = File(resultFolder, "witness-$concreteTraces.yml")
        val inputfile =
          config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!
        val property = ErrorDetection.ERROR_LOCATION
        val ltlViolationProperty = ErrorDetection.ERROR_LOCATION.ltl.toString()
        val architecture = (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture
        val witnessWriter = YamlWitnessWriter()
        witnessWriter.tracegenWitnessFromConcreteTrace(
          concrTrace,
          witnessWriter.getMetadata(inputfile, ltlViolationProperty, architecture),
          inputfile,
          property,
          ltlViolationProperty,
          parseContext!!,
          yamlWitnessFile,
        )

        logger.write(
          Logger.Level.RESULT,
          "Concrete trace exported to ${concreteTraceFile}, ${yamlWitnessFile} and ${concreteDotFile}\n",
        )
        concreteTraces++
      } catch (e: IllegalArgumentException) {
        logger.write(Logger.Level.SUBSTEP, e.toString())
        logger.write(Logger.Level.SUBSTEP, "\nContinuing concretization with next trace...\n")
      }
    }
    logger.write(
      Logger.Level.RESULT,
      "\nSuccessfully generated ${concreteTraces-1} concrete traces.\n",
    )
  }

  // TODO print coverage (full or not)?
}
