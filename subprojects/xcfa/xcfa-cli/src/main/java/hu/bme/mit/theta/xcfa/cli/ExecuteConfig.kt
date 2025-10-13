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
import hu.bme.mit.theta.common.logging.Logger.Level.*
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.coi.ConeOfInfluence
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiMultiThread
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiSingleThread
import hu.bme.mit.theta.xcfa.analysis.oc.OcDecisionProcedureType
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.analysis.por.XcfaSporLts
import hu.bme.mit.theta.xcfa.cli.checkers.getChecker
import hu.bme.mit.theta.xcfa.cli.checkers.getSafetyChecker
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.*
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.ApplyWitnessPassesManager
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.toC
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

fun runConfig(
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
  throwDontExit: Boolean,
): Result<*> {
  propagateInputOptions(config, logger, uniqueLogger)

  registerAllSolverManagers(config.backendConfig.solverHome, logger)

  validateInputOptions(config, logger, uniqueLogger)

  val (xcfa, mcm, parseContext) =
    if (config.backendConfig.inProcess && config.backendConfig.parseInProcess) {
      logger.writeln(INFO, "Not parsing input because a worker process will handle it later.")
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

  val result = backend(xcfa, mcm, parseContext, config, logger, uniqueLogger, throwDontExit)

  postAnalysisLogging(xcfa, result, mcm, parseContext, config, logger, uniqueLogger)

  return result
}

private fun propagateInputOptions(config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger) {
  config.inputConfig.property = determineProperty(config, logger)
  LbePass.level = config.frontendConfig.lbeLevel
  StaticCoiPass.enabled = config.frontendConfig.staticCoi
  if (config.backendConfig.backend == Backend.CEGAR) {
    val cegarConfig = config.backendConfig.specConfig
    cegarConfig as CegarConfig
    val random = Random(cegarConfig.porRandomSeed)
    XcfaSporLts.random = random
    XcfaDporLts.random = random
  }
  if (
    config.inputConfig.property == ErrorDetection.MEMSAFETY ||
      config.inputConfig.property == ErrorDetection.MEMCLEANUP
  ) {
    MemsafetyPass.NEED_CHECK = true
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
  rule("NoCoiWhenDataRace") {
    config.backendConfig.backend == Backend.CEGAR &&
      (config.backendConfig.specConfig as? CegarConfig)?.coi != ConeOfInfluenceMode.NO_COI &&
      config.inputConfig.property == ErrorDetection.DATA_RACE
  }
  rule("NoAaporWhenDataRace") {
    (config.backendConfig.specConfig as? CegarConfig)?.porLevel?.isAbstractionAware == true &&
      config.inputConfig.property == ErrorDetection.DATA_RACE
  }
  rule("DPORWithoutDFS") {
    (config.backendConfig.specConfig as? CegarConfig)?.porLevel?.isDynamic == true &&
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
      (config.backendConfig.specConfig as? OcConfig)?.smtSolver != "Z3:4.13"
  }
}

fun frontend(
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
): Triple<XCFA, MCM, ParseContext> {
  if (config.inputConfig.xcfaWCtx != null) {
    val xcfa = config.inputConfig.xcfaWCtx!!.first
    ConeOfInfluence =
      if (config.inputConfig.xcfaWCtx!!.third.multiThreading) {
        XcfaCoiMultiThread(xcfa)
      } else {
        XcfaCoiSingleThread(xcfa)
      }
    return config.inputConfig.xcfaWCtx!!
  }

  val stopwatch = Stopwatch.createStarted()

  val input = config.inputConfig.input!!
  logger.write(
    Logger.Level.INFO,
    "Parsing the input $input as ${config.frontendConfig.inputType}\n",
  )

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

  ConeOfInfluence =
    if (parseContext.multiThreading) XcfaCoiMultiThread(xcfa) else XcfaCoiSingleThread(xcfa)

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

  logger.write(
    Logger.Level.INFO,
    "Frontend finished: ${xcfa.name}  (in ${
        stopwatch.elapsed(TimeUnit.MILLISECONDS)
    } ms)\n",
  )

  logger.write(RESULT, "ParsingResult Success\n")
  logger.write(
    RESULT,
    "Alias graph size: ${xcfa.pointsToGraph.size} -> ${xcfa.pointsToGraph.values.map { it.size }.toList()}\n",
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
      xcfa?.procedures?.all {
        it.errorLoc.isEmpty && config.inputConfig.property == ErrorDetection.ERROR_LOCATION
      } ?: false
    ) {
      val result = SafetyResult.safe<EmptyProof, EmptyCex>(EmptyProof.getInstance())
      logger.write(Logger.Level.RESULT, "Input is trivially safe\n")

      logger.write(RESULT, result.toString() + "\n")
      result
    } else {
      val stopwatch = Stopwatch.createStarted()

      logger.write(
        Logger.Level.INFO,
        "Starting verification of ${if (xcfa?.name == "") "UnnamedXcfa" else (xcfa?.name ?: "DeferredXcfa")} using ${config.backendConfig.backend}\n${config}\n",
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
                logger.write(RESULT, "Incomplete loop unroll used: safe result is unreliable.\n")
                if (config.outputConfig.acceptUnreliableSafe)
                  result // for comparison with BMC tools
                else SafetyResult.unknown<EmptyProof, EmptyCex>()
              }

              result.isUnsafe -> {
                // need to determine what kind
                val property =
                  try {
                    ErrorDetection.ltlFromTrace(
                      config.inputConfig.property,
                      result.asUnsafe().cex as? Trace<XcfaState<*>, XcfaAction>,
                    )
                  } catch (e: UnknownResultException) {
                    return@ResultMapper SafetyResult.unknown<EmptyProof, EmptyCex>()
                  }
                property?.also { logger.write(RESULT, "(Property %s)\n", it) }
                result
              }

              else -> {
                result
              }
            }
          }

      logger.write(
        INFO,
        "Backend finished (in ${
                stopwatch.elapsed(TimeUnit.MILLISECONDS)
            } ms)\n",
      )

      logger.write(RESULT, result.toString() + "\n")
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
  if (config.outputConfig.enableOutput) {
    try {
      val resultFolder = config.outputConfig.resultFolder
      resultFolder.mkdirs()

      logger.write(
        Logger.Level.INFO,
        "Writing pre-verification artifacts to directory ${resultFolder.absolutePath} with config ${config.outputConfig}\n",
      )

      if (!config.outputConfig.chcOutputConfig.disable) {
        xcfa.procedures.forEach {
          try {
            val chcFile = File(resultFolder, "xcfa-${it.name}.smt2")
            chcFile.writeText(
              it.toSMT2CHC(
                config.inputConfig.property == ErrorDetection.TERMINATION,
                (config.backendConfig.specConfig as? HornConfig)?.rankingFuncConstr
                  ?: RankingFunction.ADD,
              )
            )
          } catch (e: Exception) {
            logger.write(INFO, "Could not write CHC file: " + e.stackTraceToString())
          }
        }
      }

      if (!config.outputConfig.xcfaOutputConfig.disable) {
        val xcfaDotFile = File(resultFolder, "xcfa.dot")
        xcfaDotFile.writeText(xcfa.toDot())

        val xcfaJsonFile = File(resultFolder, "xcfa.json")
        val uglyJson = getGson(xcfa).toJson(xcfa)
        val create = GsonBuilder().setPrettyPrinting().create()
        xcfaJsonFile.writeText(create.toJson(JsonParser.parseString(uglyJson)))
      }

      if (!config.outputConfig.cOutputConfig.disable) {
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
          logger.write(Logger.Level.VERBOSE, "Could not emit C file\n")
        }
      }
    } catch (e: Throwable) {
      logger.write(Logger.Level.INFO, "Could not output files: ${e.stackTraceToString()}\n")
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
  if (
    config.frontendConfig.inputType == InputType.CHC &&
      xcfa != null &&
      (config.frontendConfig.specConfig as CHCFrontendConfig).model
  ) {
    val resultFolder = config.outputConfig.resultFolder
    resultFolder.mkdirs()
    val chcAnswer = writeModel(xcfa, safetyResult)
    val chcAnswerFile = File(resultFolder, "chc-answer.smt2")
    if (chcAnswerFile.exists()) {
      logger.writeln(
        INFO,
        "CHC answer/model already written to file $chcAnswerFile, not overwriting",
      )
    } else {
      chcAnswerFile.writeText(chcAnswer)
      logger.writeln(INFO, "CHC answer/model written to file $chcAnswerFile")
    }
  }
  if (config.outputConfig.enableOutput && mcm != null && parseContext != null) {
    try {
      // we only want to log the files if the current configuration is not --in-process or portfolio
      if (config.backendConfig.inProcess || config.backendConfig.backend == Backend.PORTFOLIO) {
        return
      }

      val resultFolder = config.outputConfig.resultFolder
      resultFolder.mkdirs()

      logger.write(
        Logger.Level.INFO,
        "Writing post-verification artifacts to directory ${resultFolder.absolutePath}\n",
      )

      // TODO eliminate the need for the instanceof check
      if (
        !config.outputConfig.argConfig.disable && safetyResult.proof is ARG<out State, out Action>
      ) {
        val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
        val g: Graph =
          ArgVisualizer.getDefault().visualize(safetyResult.proof as ARG<out State, out Action>)
        argFile.writeText(GraphvizWriter.getInstance().writeString(g))
      }

      if (!config.outputConfig.witnessConfig.disable) {
        if (
          safetyResult.isUnsafe &&
            safetyResult.asUnsafe().cex != null &&
            !config.outputConfig.witnessConfig.svcomp
        ) {
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

          val traceFile = File(resultFolder, "trace.dot")
          val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
          traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))

          val sequenceFile = File(resultFolder, "trace.plantuml")
          writeSequenceTrace(sequenceFile, trace as Trace<XcfaState<ExplState>, XcfaAction>) {
            (_, act) ->
            act.label.getFlatLabels().map(XcfaLabel::toString)
          }

          val optSequenceFile = File(resultFolder, "trace-optimized.plantuml")
          writeSequenceTrace(optSequenceFile, concrTrace) { (_, act) ->
            act.label.getFlatLabels().map(XcfaLabel::toString)
          }

          val cSequenceFile = File(resultFolder, "trace-c.plantuml")
          writeSequenceTrace(cSequenceFile, concrTrace) { (state, act) ->
            val proc = state.processes[act.pid]
            val loc = proc?.locs?.peek()
            (loc?.metadata as? CMetaData)?.sourceText?.split("\n") ?: listOf("<unknown>")
          }
        }
        val ltlViolationProperty =
          ErrorDetection.ltlFromTrace(
            config.inputConfig.property,
            safetyResult.asUnsafe().cex as? Trace<XcfaState<*>, XcfaAction>,
          )!!
        val witnessFile = File(resultFolder, "witness.graphml")
        GraphmlWitnessWriter()
          .writeWitness(
            safetyResult,
            config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
            getSolver(
              config.outputConfig.witnessConfig.concretizerSolver,
              config.outputConfig.witnessConfig.validateConcretizerSolver,
            ),
            parseContext,
            witnessFile,
            config.inputConfig.property,
            ltlViolationProperty,
          )
        val yamlWitnessFile = File(resultFolder, "witness.yml")
        YamlWitnessWriter()
          .writeWitness(
            safetyResult,
            config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
            config.inputConfig.property,
            ltlViolationProperty,
            (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture,
            getSolver(
              config.outputConfig.witnessConfig.concretizerSolver,
              config.outputConfig.witnessConfig.validateConcretizerSolver,
            ),
            parseContext,
            yamlWitnessFile,
          )
      }
    } catch (e: Throwable) {
      logger.write(Logger.Level.INFO, "Could not output files: ${e.stackTraceToString()}\n")
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
        val ltlProperty = ErrorDetection.ERROR_LOCATION.ltl(Unit)!!
        val architecture = (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture
        val witnessWriter = YamlWitnessWriter()
        witnessWriter.tracegenWitnessFromConcreteTrace(
          concrTrace,
          witnessWriter.getMetadata(inputfile, ltlProperty, architecture),
          inputfile,
          property,
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
