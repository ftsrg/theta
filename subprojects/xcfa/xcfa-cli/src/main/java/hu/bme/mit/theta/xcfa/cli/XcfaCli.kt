/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import com.beust.jcommander.JCommander
import com.beust.jcommander.Parameter
import com.beust.jcommander.ParameterException
import com.google.common.base.Stopwatch
import com.google.gson.Gson
import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.chc.ChcFrontend
import hu.bme.mit.theta.llvm2xcfa.ArithmeticType
import hu.bme.mit.theta.llvm2xcfa.XcfaUtils.fromFile
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.cli.utils.XcfaWitnessWriter
import hu.bme.mit.theta.xcfa.cli.witnesses.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.LoopUnrollPass
import org.antlr.v4.runtime.CharStreams
import java.io.File
import java.io.FileInputStream
import java.io.FileReader
import java.util.*
import java.util.concurrent.TimeUnit
import javax.script.Bindings
import javax.script.ScriptEngine
import javax.script.ScriptEngineManager
import javax.script.SimpleBindings
import kotlin.random.Random
import kotlin.system.exitProcess


class XcfaCli(private val args: Array<String>) {

    //////////// CONFIGURATION OPTIONS BEGIN ////////////
    //////////// input task ////////////
    @Parameter(names = ["--input"], description = "Path of the input C program", required = true)
    var input: File? = null

    @Parameter(names = ["--property"], description = "Path of the property file")
    var property: File? = null

    @Parameter(names = ["--lbe"],
        description = "Level of LBE (NO_LBE, LBE_LOCAL, LBE_SEQ, LBE_FULL)")
    var lbeLevel: LbePass.LbeLevel = LbePass.LbeLevel.LBE_SEQ

    @Parameter(names = ["--unroll"], description = "Max number of loop iterations to unroll")
    var loopUnroll: Int = 50

    @Parameter(names = ["--input-type"], description = "Format of the input")
    var inputType: InputType = InputType.C

    @Parameter(names = ["--chc-transformation"], description = "Direction of transformation from CHC to XCFA")
    var chcTransformation: ChcFrontend.ChcTransformation = ChcFrontend.ChcTransformation.PORTFOLIO

    //////////// backend options ////////////
    @Parameter(names = ["--backend"], description = "Backend analysis to use")
    var backend: Backend = Backend.CEGAR

    @Parameter(names = ["--strategy"], description = "Execution strategy")
    var strategy: Strategy = Strategy.DIRECT

    @Parameter(names = ["--portfolio"],
        description = "Portfolio type (only valid with --strategy PORTFOLIO)")
    var portfolio: File = File("complex.kts")

    @Parameter(names = ["--smt-home"], description = "The path of the solver registry")
    var solverHome: String = SmtLibSolverManager.HOME.toAbsolutePath().toString()

    @Parameter(names = ["--debug"], description = "Debug mode (not exiting when encountering an exception)")
    var debug: Boolean = false

    //////////// debug options ////////////
    @Parameter(names = ["--stacktrace"],
        description = "Print full stack trace in case of exception")
    var stacktrace: Boolean = false

    @Parameter(names = ["--no-analysis", "--parse-only"],
        description = "Executes the model transformation to XCFA and CFA, and then exits; use with --output-results to get data about the (X)CFA")
    var noAnalysis = false

    @Parameter(names = ["--print-config"],
        description = "Print the config to a JSON file (takes a filename as argument)")
    var printConfigFile: File? = null

    //////////// output data and statistics ////////////
    @Parameter(names = ["--version"], description = "Display version", help = true)
    var versionInfo = false

    @Parameter(names = ["--loglevel"], description = "Detailedness of logging")
    var logLevel = Logger.Level.MAINSTEP

    @Parameter(names = ["--output-results"],
        description = "Creates a directory, in which it outputs the xcfa, cex and witness")
    var outputResults = false

    @Parameter(names = ["--output-directory"],
        description = "Specify the directory where the result files are stored")
    var resultFolder: File = File("results-${Date()}")

    @Parameter(names = ["--witness-only"],
        description = "Does not output any other files, just a violation/correctness witness only")
    var svcomp = false

    @Parameter(names = ["--cex-solver"], description = "Concretizer solver name")
    var concretizerSolver: String = "Z3"

    @Parameter(names = ["--validate-cex-solver"],
        description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateConcretizerSolver: Boolean = false

    @Parameter(names = ["--seed"], description = "Random seed used for DPOR")
    var randomSeed: Int = -1

    @Parameter(names = ["--arg-to-file"], description = "Visualize the resulting file here: https://ftsrg-edu.github.io/student-sisak-argviz/")
    var argToFile: Boolean = false

    @Parameter
    var remainingFlags: MutableList<String> = ArrayList()

    private fun run() {
        /// Checking flags
        try {
            JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(*args)
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            ex.printStackTrace()
            ex.usage()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        }

        /// version
        if (versionInfo) {
            CliUtils.printVersion(System.out)
            return
        }
        val stopwatch = Stopwatch.createStarted()
        val gsonForOutput = getGson()
        val logger = ConsoleLogger(logLevel)
        val explicitProperty: ErrorDetection = getExplicitProperty()

        // propagating input variables
        LbePass.level = lbeLevel
        if (randomSeed >= 0) XcfaDporLts.random = Random(randomSeed)
        if (argToFile) {
            WebDebuggerLogger.enableWebDebuggerLogger()
            WebDebuggerLogger.getInstance().setTitle(input?.name)
        }
        LoopUnrollPass.UNROLL_LIMIT = loopUnroll


        logger.write(Logger.Level.INFO, "Parsing the input $input as $inputType")
        val parseContext = ParseContext()
        val xcfa = getXcfa(logger, explicitProperty, parseContext)
        logger.write(Logger.Level.INFO, "Frontend finished: ${xcfa.name}  (in ${
            stopwatch.elapsed(TimeUnit.MILLISECONDS)
        } ms)\n")

        preVerificationLogging(logger, xcfa, gsonForOutput)

        if (noAnalysis) {
            logger.write(Logger.Level.RESULT, "ParsingResult Success")
            return
        }
        // verification
        stopwatch.reset().start()
        logger.write(Logger.Level.INFO, "Starting verification of ${xcfa.name} using $backend")
        registerAllSolverManagers(solverHome, logger)
        val config = parseConfigFromCli()
        if (strategy != Strategy.PORTFOLIO && printConfigFile != null) {
            printConfigFile!!.writeText(gsonForOutput.toJson(config))
        }
        val safetyResult: SafetyResult<*, *> =
            when (strategy) {
                Strategy.DIRECT -> runDirect(xcfa, config, logger)
                Strategy.SERVER -> runServer(xcfa, config, logger, parseContext)
                Strategy.SERVER_DEBUG -> runServerDebug(xcfa, config, logger, parseContext)
                Strategy.PORTFOLIO -> runPortfolio(xcfa, explicitProperty, logger, parseContext, debug)
            }
        // post verification
        postVerificationLogging(safetyResult, parseContext)
        logger.write(Logger.Level.RESULT, safetyResult.toString() + "\n")
    }

    private fun runDirect(xcfa: XCFA, config: XcfaCegarConfig, logger: ConsoleLogger) =
        exitOnError(stacktrace, debug) { config.check(xcfa, logger) }

    private fun runServer(xcfa: XCFA, config: XcfaCegarConfig,
        logger: ConsoleLogger, parseContext: ParseContext): SafetyResult<*, *> {
        val safetyResultSupplier = config.checkInProcess(xcfa, solverHome, true,
            input!!.absolutePath, logger, parseContext)
        return try {
            safetyResultSupplier()
        } catch (e: ErrorCodeException) {
            exitProcess(e.code)
        }
    }

    private fun runServerDebug(xcfa: XCFA, config: XcfaCegarConfig,
        logger: ConsoleLogger, parseContext: ParseContext): SafetyResult<*, *> {
        val safetyResultSupplier = config.checkInProcessDebug(xcfa, solverHome, true,
            input!!.absolutePath, logger, parseContext)
        return try {
            safetyResultSupplier()
        } catch (e: ErrorCodeException) {
            exitProcess(e.code)
        }
    }

    private fun runPortfolio(xcfa: XCFA, explicitProperty: ErrorDetection,
        logger: ConsoleLogger, parseContext: ParseContext, debug: Boolean = false): SafetyResult<*, *> {
        val portfolioDescriptor = portfolio
        val kotlinEngine: ScriptEngine = ScriptEngineManager().getEngineByExtension("kts")
        return try {
            val bindings: Bindings = SimpleBindings()
            bindings["xcfa"] = xcfa
            bindings["parseContext"] = parseContext
            bindings["property"] = explicitProperty
            bindings["cFileName"] = input!!.absolutePath
            bindings["logger"] = logger
            bindings["smtHome"] = solverHome
            bindings["traits"] = VerificationTraits(
                multithreaded = parseContext.multiThreading,
                arithmetic = parseContext.bitwiseOption,
            )
            val portfolioResult = kotlinEngine.eval(FileReader(portfolioDescriptor),
                bindings) as Pair<XcfaCegarConfig, SafetyResult<*, *>>

            concretizerSolver = portfolioResult.first.refinementSolver
            validateConcretizerSolver = portfolioResult.first.validateRefinementSolver

            portfolioResult.second
        } catch (e: ErrorCodeException) {
            if (debug) throw e
            exitProcess(e.code)
        } catch (e: Exception) {
            if (debug) throw e
            logger.write(Logger.Level.RESULT,
                "Portfolio from $portfolioDescriptor could not be executed.")
            e.printStackTrace()
            exitProcess(ExitCodes.PORTFOLIO_ERROR.code)
        }
    }

    private fun preVerificationLogging(logger: ConsoleLogger, xcfa: XCFA, gsonForOutput: Gson) {
        if (outputResults && !svcomp) {
            resultFolder.mkdirs()

            logger.write(Logger.Level.INFO,
                "Writing results to directory ${resultFolder.absolutePath}")

            val xcfaDotFile = File(resultFolder, "xcfa.dot")
            xcfaDotFile.writeText(xcfa.toDot())

            val xcfaJsonFile = File(resultFolder, "xcfa.json")
            val uglyJson = gsonForOutput.toJson(xcfa)
            val create = GsonBuilder().setPrettyPrinting().create()
            xcfaJsonFile.writeText(create.toJson(JsonParser.parseString(uglyJson)))
        }
    }

    private fun postVerificationLogging(safetyResult: SafetyResult<*, *>, parseContext: ParseContext) {
        if (svcomp || outputResults) {
            if (!svcomp) {
                resultFolder.mkdirs()

                val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
                val g: Graph = ArgVisualizer.getDefault().visualize(safetyResult.arg)
                argFile.writeText(GraphvizWriter.getInstance().writeString(g))

                if (safetyResult.isUnsafe) {
                    val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> = XcfaTraceConcretizer.concretize(
                        safetyResult.asUnsafe().trace as Trace<XcfaState<*>, XcfaAction>?,
                        getSolver(concretizerSolver, validateConcretizerSolver))

                    val traceFile = File(resultFolder, "trace.dot")
                    val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
                    traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
                }

            } else {
                XcfaWitnessWriter().writeWitness(safetyResult, input!!,
                    getSolver(concretizerSolver, validateConcretizerSolver), parseContext)
            }
        }
    }

    private fun getXcfa(logger: ConsoleLogger, explicitProperty: ErrorDetection, parseContext: ParseContext) =
        try {
            when (inputType) {
                InputType.CHC -> {
                    parseChc(logger)
                }

                InputType.C -> {
                    val stream = FileInputStream(input!!)
                    val xcfaFromC = getXcfaFromC(stream, parseContext, false,
                        explicitProperty == ErrorDetection.OVERFLOW).first
                    logger.write(Logger.Level.RESULT,
                        "Arithmetic: ${parseContext.arithmetic}\n")
                    xcfaFromC
                }

                InputType.LLVM -> fromFile(input!!, ArithmeticType.efficient)

                InputType.JSON -> {
                    val gson = getGson()
                    gson.fromJson(input!!.readText(), XCFA::class.java)
                }

                InputType.DSL -> {
                    val kotlinEngine: ScriptEngine = ScriptEngineManager().getEngineByExtension(
                        "kts")
                    kotlinEngine.eval(FileReader(input!!)) as XCFA
                }
            }
        } catch (e: Exception) {
            if (stacktrace) e.printStackTrace()
            logger.write(Logger.Level.RESULT, "Frontend failed!\n")
            exitProcess(ExitCodes.FRONTEND_FAILED.code)
        }

    private fun parseChc(logger: ConsoleLogger): XCFA {
        var chcFrontend: ChcFrontend
        val xcfaBuilder = if (chcTransformation == ChcFrontend.ChcTransformation.PORTFOLIO) { // try forward, fallback to backward
            chcFrontend = ChcFrontend(ChcFrontend.ChcTransformation.FORWARD)
            try {
                chcFrontend.buildXcfa(CharStreams.fromStream(FileInputStream(input!!)))
            } catch (e: UnsupportedOperationException) {
                logger.write(Logger.Level.INFO, "Non-linear CHC found, retrying using backward transformation...")
                chcFrontend = ChcFrontend(ChcFrontend.ChcTransformation.BACKWARD)
                chcFrontend.buildXcfa(CharStreams.fromStream(FileInputStream(input!!)))
            }
        } else {
            chcFrontend = ChcFrontend(chcTransformation)
            chcFrontend.buildXcfa(CharStreams.fromStream(FileInputStream(input!!)))
        }
        return xcfaBuilder.build()
    }

    private fun getExplicitProperty() = if (property != null) {
        remainingFlags.add("--error-detection")
        when {
            property!!.name.endsWith("unreach-call.prp") -> {
                remainingFlags.add(ErrorDetection.ERROR_LOCATION.toString())
                ErrorDetection.ERROR_LOCATION
            }

            property!!.name.endsWith("no-data-race.prp") -> {
                remainingFlags.add(ErrorDetection.DATA_RACE.toString())
                if (lbeLevel != LbePass.LbeLevel.NO_LBE) {
                    System.err.println(
                        "Changing LBE type to NO_LBE because the DATA_RACE property will be erroneous otherwise")
                    lbeLevel = LbePass.LbeLevel.NO_LBE
                }
                ErrorDetection.DATA_RACE
            }

            property!!.name.endsWith("no-overflow.prp") -> {
                remainingFlags.add(ErrorDetection.OVERFLOW.toString())
                if (lbeLevel != LbePass.LbeLevel.NO_LBE) {
                    System.err.println(
                        "Changing LBE type to NO_LBE because the OVERFLOW property will be erroneous otherwise")
                    lbeLevel = LbePass.LbeLevel.NO_LBE
                }
                ErrorDetection.OVERFLOW
            }

            else -> {
                remainingFlags.add(ErrorDetection.NO_ERROR.toString())
                System.err.println(
                    "Unknown property $property, using full state space exploration (no refinement)")
                ErrorDetection.NO_ERROR
            }
        }
    } else ErrorDetection.ERROR_LOCATION

    private fun parseConfigFromCli(): XcfaCegarConfig {
        val cegarConfig = XcfaCegarConfig()
        try {
            JCommander.newBuilder().addObject(cegarConfig).programName(JAR_NAME).build()
                .parse(*remainingFlags.toTypedArray())
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            ex.printStackTrace()
            ex.usage()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        }
        return cegarConfig
    }

    companion object {

        private const val JAR_NAME = "theta-xcfa-cli.jar"

        @JvmStatic
        fun main(args: Array<String>) {
            val mainApp = XcfaCli(args)
            mainApp.run()
        }
    }
}