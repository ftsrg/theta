/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.debug.ARGWebDebugger
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.cat.dsl.CatDslManager
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level.RESULT
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.coi.ConeOfInfluence
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiMultiThread
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiSingleThread
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.analysis.por.XcfaSporLts
import hu.bme.mit.theta.xcfa.cli.checkers.getChecker
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.*
import hu.bme.mit.theta.xcfa.cli.witnesses.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass
import hu.bme.mit.theta.xcfa.toC
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.random.Random

fun runConfig(
    config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger,
    throwDontExit: Boolean
): SafetyResult<*, *> {
    propagateInputOptions(config, logger, uniqueLogger)

    registerAllSolverManagers(config.backendConfig.solverHome, logger)

    validateInputOptions(config, logger, uniqueLogger)

    val (xcfa, mcm, parseContext) = frontend(config, logger, uniqueLogger)

    preVerificationLogging(xcfa, mcm, parseContext, config, logger, uniqueLogger)

    val result = backend(xcfa, mcm, parseContext, config, logger, uniqueLogger, throwDontExit)

    postVerificationLogging(result, mcm, parseContext, config, logger, uniqueLogger)

    return result
}


private fun propagateInputOptions(config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger) {
    config.inputConfig.property = determineProperty(config, logger)
    LbePass.level = config.frontendConfig.lbeLevel
    if (config.backendConfig.backend == Backend.CEGAR) {
        val cegarConfig = config.backendConfig.specConfig
        cegarConfig as CegarConfig
        val random = Random(cegarConfig.porRandomSeed)
        XcfaSporLts.random = random
        XcfaDporLts.random = random
    }
    if (config.debugConfig.argToFile) {
        WebDebuggerLogger.enableWebDebuggerLogger()
        WebDebuggerLogger.getInstance().setTitle(config.inputConfig.input?.name)
    }

    LoopUnrollPass.UNROLL_LIMIT = config.frontendConfig.loopUnroll
    LoopUnrollPass.FORCE_UNROLL_LIMIT = config.frontendConfig.forceUnroll
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
        config.frontendConfig.loopUnroll != -1 && config.frontendConfig.loopUnroll < config.frontendConfig.forceUnroll
    }
    // TODO add more validation options
}

fun frontend(config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger): Triple<XCFA, MCM, ParseContext> {
    if (config.inputConfig.xcfaWCtx != null) {
        val xcfa = config.inputConfig.xcfaWCtx!!.first
        ConeOfInfluence = if (config.inputConfig.xcfaWCtx!!.third.multiThreading) {
            XcfaCoiMultiThread(xcfa)
        } else {
            XcfaCoiSingleThread(xcfa)
        }
        return config.inputConfig.xcfaWCtx!!
    }

    val stopwatch = Stopwatch.createStarted()

    val input = config.inputConfig.input!!
    logger.write(Logger.Level.INFO, "Parsing the input $input as ${config.frontendConfig.inputType}\n")

    val parseContext = ParseContext()

    if (config.frontendConfig.inputType == InputType.C) {
        val cConfig = config.frontendConfig.specConfig
        cConfig as CFrontendConfig
        parseContext.arithmetic = cConfig.arithmetic
    }

    val xcfa = getXcfa(config, parseContext, logger, uniqueLogger)

    val mcm = if (config.inputConfig.catFile != null) {
        CatDslManager.createMCM(config.inputConfig.catFile!!)
    } else {
        emptySet()
    }

    ConeOfInfluence = if (parseContext.multiThreading) XcfaCoiMultiThread(xcfa) else XcfaCoiSingleThread(xcfa)

    logger.write(
        Logger.Level.INFO, "Frontend finished: ${xcfa.name}  (in ${
            stopwatch.elapsed(TimeUnit.MILLISECONDS)
        } ms)\n"
    )

    logger.write(RESULT, "ParsingResult Success\n")

    return Triple(xcfa, mcm, parseContext)
}

private fun backend(
    xcfa: XCFA, mcm: MCM, parseContext: ParseContext, config: XcfaConfig<*, *>,
    logger: Logger,
    uniqueLogger: Logger,
    throwDontExit: Boolean
): SafetyResult<*, *> =
    if (config.backendConfig.backend == Backend.NONE) {
        SafetyResult.unknown<State, Action>()
    } else {
        if (xcfa.procedures.all { it.errorLoc.isEmpty && config.inputConfig.property == ErrorDetection.ERROR_LOCATION }) {
            val result = SafetyResult.safe<State, Action>()
            logger.write(Logger.Level.INFO, "Input is trivially safe\n")

            logger.write(RESULT, result.toString() + "\n")
            result
        } else {
            val stopwatch = Stopwatch.createStarted()

            logger.write(
                Logger.Level.INFO,
                "Starting verification of ${if (xcfa.name == "") "UnnamedXcfa" else xcfa.name} using ${config.backendConfig.backend}\n"
            )

            val checker = getChecker(xcfa, mcm, config, parseContext, logger, uniqueLogger)
            val result = exitOnError(config.debugConfig.stacktrace, config.debugConfig.debug || throwDontExit) {
                checker.check()
            }.let { result ->
                when {
                    result.isSafe && LoopUnrollPass.FORCE_UNROLL_USED -> { // cannot report safe if force unroll was used
                        logger.write(RESULT, "Incomplete loop unroll used: safe result is unreliable.\n")
                        SafetyResult.unknown<State, Action>()
                    }

                    result.isUnsafe && result.asUnsafe().trace.actions.any { it.label.dereferences.isNotEmpty() } -> {
                        logger.write(RESULT, "Program contains dereferences, unsafe result is unreliable.\n")
                        SafetyResult.unknown()
                    }

                    else -> result
                }
            }

            logger.write(
                Logger.Level.INFO, "Backend finished (in ${
                    stopwatch.elapsed(TimeUnit.MILLISECONDS)
                } ms)\n"
            )

            logger.write(RESULT, result.toString() + "\n")
            result
        }
    }

private fun preVerificationLogging(
    xcfa: XCFA, mcm: MCM, parseContext: ParseContext, config: XcfaConfig<*, *>,
    logger: Logger, uniqueLogger: Logger
) {
    if (config.outputConfig.enableOutput) {
        try {
            val resultFolder = config.outputConfig.resultFolder
            resultFolder.mkdirs()

            logger.write(
                Logger.Level.INFO,
                "Writing pre-verification artifacts to directory ${resultFolder.absolutePath}\n"
            )

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
                            parseContext, config.outputConfig.cOutputConfig.useArr,
                            config.outputConfig.cOutputConfig.useExArr, config.outputConfig.cOutputConfig.useRange
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

private fun postVerificationLogging(
    safetyResult: SafetyResult<*, *>, mcm: MCM,
    parseContext: ParseContext, config: XcfaConfig<*, *>, logger: Logger, uniqueLogger: Logger
) {
    if (config.outputConfig.enableOutput) {
        try {
            // we only want to log the files if the current configuration is not --in-process or portfolio
            if (config.backendConfig.inProcess || config.backendConfig.backend == Backend.PORTFOLIO) {
                return
            }

            val resultFolder = config.outputConfig.resultFolder
            resultFolder.mkdirs()

            logger.write(
                Logger.Level.INFO,
                "Writing post-verification artifacts to directory ${resultFolder.absolutePath}\n"
            )

            if (!config.outputConfig.argConfig.disable && safetyResult.hasArg()) {
                val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
                val g: Graph = ArgVisualizer.getDefault().visualize(safetyResult.arg)
                argFile.writeText(GraphvizWriter.getInstance().writeString(g))
            }

            if (!config.outputConfig.witnessConfig.disable) {
                if (safetyResult.isUnsafe && safetyResult.asUnsafe().trace != null) {
                    val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> = XcfaTraceConcretizer.concretize(
                        safetyResult.asUnsafe().trace as Trace<XcfaState<*>, XcfaAction>?,
                        getSolver(
                            config.outputConfig.witnessConfig.concretizerSolver,
                            config.outputConfig.witnessConfig.validateConcretizerSolver
                        )
                    )

                    val traceFile = File(resultFolder, "trace.dot")
                    val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
                    traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
                }
                val witnessFile = File(resultFolder, "witness.graphml")
                XcfaWitnessWriter().writeWitness(
                    safetyResult, config.inputConfig.input!!,
                    getSolver(
                        config.outputConfig.witnessConfig.concretizerSolver,
                        config.outputConfig.witnessConfig.validateConcretizerSolver
                    ), parseContext, witnessFile
                )
            }
        } catch (e: Throwable) {
            logger.write(Logger.Level.INFO, "Could not output files: ${e.stackTraceToString()}\n")
        }
    }
}