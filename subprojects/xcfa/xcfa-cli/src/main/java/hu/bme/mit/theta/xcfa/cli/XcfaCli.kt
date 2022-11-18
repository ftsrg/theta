/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseChecker
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.cli.utils.XcfaWitnessWriter
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.passes.LbePass
import java.io.File
import java.io.FileInputStream
import java.io.FileReader
import java.util.*
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import javax.script.Bindings
import javax.script.ScriptEngine
import javax.script.ScriptEngineManager
import javax.script.SimpleBindings
import kotlin.system.exitProcess


class XcfaCli(private val args: Array<String>) {
    //////////// CONFIGURATION OPTIONS BEGIN ////////////
    //////////// input task ////////////
    @Parameter(names = ["--input"], description = "Path of the input C program", required = true)
    var input: File? = null

    @Parameter(names = ["--lbe"], description = "Level of LBE (NO_LBE, LBE_LOCAL, LBE_SEQ, LBE_FULL)")
    var lbeLevel: LbePass.LBELevel = LbePass.LBELevel.LBE_SEQ

    //////////// backend options ////////////
    @Parameter(names = ["--backend"], description = "Backend analysis to use")
    var backend: Backend = Backend.CEGAR

    @Parameter(names = ["--strategy"], description = "Execution strategy")
    var strategy: Strategy = Strategy.PORTFOLIO

    @Parameter(names = ["--portfolio"], description = "Portfolio type (only valid with --strategy PORTFOLIO)")
    var portfolio: Portfolio = Portfolio.COMPLEX

    @Parameter(names = ["--smt-home"], description = "The path of the solver registry")
    var solverHome: String = SmtLibSolverManager.HOME.toAbsolutePath().toString()

    //////////// debug options ////////////
    @Parameter(names = ["--stacktrace"], description = "Print full stack trace in case of exception")
    var stacktrace: Boolean = false

    @Parameter(names = ["--no-analysis"], description = "Executes the model transformation to XCFA and CFA, and then exits; use with --output-results to get data about the (X)CFA")
    var noAnalysis = false

    @Parameter(names = ["--print-config"], description = "Print the config to a JSON file (takes a filename as argument)")
    var printConfigFile: String? = null


    //////////// output data and statistics ////////////
    @Parameter(names = ["--version"], description = "Display version", help = true)
    var versionInfo = false

    @Parameter(names = ["--loglevel"], description = "Detailedness of logging")
    var logLevel = Logger.Level.MAINSTEP

    @Parameter(names = ["--output-results"], description = "Creates a directory, in which it outputs the xcfa, cex and witness")
    var outputResults = false

    @Parameter(names = ["--output-directory"], description = "Specify the directory where the result files are stored")
    var resultFolder: File = File("results-${Date()}")

    @Parameter(names = ["--witness-only"], description = "Does not output any other files, just a violation/correctness witness only")
    var svcomp = false

    @Parameter(names = ["--cex-solver"], description = "Concretizer solver name")
    var concretizerSolver: String = "Z3"

    @Parameter(names = ["--validate-cex-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateConcretizerSolver: Boolean = false

    @Parameter
    var remainingFlags: List<String> = ArrayList()

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
        val logger = ConsoleLogger(logLevel)

        /// Starting frontend
        val swFrontend = Stopwatch.createStarted()
        LbePass.level = lbeLevel

        val xcfa = try {
            val stream = FileInputStream(input!!)
            val xcfaFromC = getXcfaFromC(stream)
            logger.write(Logger.Level.INFO, "Frontend finished: ${xcfaFromC.name}  (in ${swFrontend.elapsed(TimeUnit.MILLISECONDS)} ms)\n")
            logger.write(Logger.Level.RESULT, "Arithmetic: ${BitwiseChecker.getBitwiseOption()}\n")
            xcfaFromC
        } catch (e: Exception) {
            if (stacktrace) e.printStackTrace();
            logger.write(Logger.Level.RESULT, "Frontend failed!\n")
            exitProcess(ExitCodes.FRONTEND_FAILED.code)
        }
        swFrontend.reset().start()

        val gsonForOutput = getGson()

        if (svcomp || outputResults) {
            if (!svcomp) {
                resultFolder.mkdirs()

                logger.write(Logger.Level.INFO, "Writing results to directory ${resultFolder.absolutePath}")

                val xcfaDotFile = File(resultFolder, "xcfa.dot")
                xcfaDotFile.writeText(xcfa.toDot())

                val xcfaJsonFile = File(resultFolder, "xcfa.json")
                val uglyJson = gsonForOutput.toJson(xcfa)
                val create = GsonBuilder().setPrettyPrinting().create()
                xcfaJsonFile.writeText(create.toJson(JsonParser.parseString(uglyJson)))
            }
        }

        if (noAnalysis) {
            logger.write(Logger.Level.RESULT, "ParsingResult Success")
            return
        }
        registerAllSolverManagers(solverHome, logger)

        val safetyResult: SafetyResult<*, *> =
                when (strategy) {
                    Strategy.DIRECT -> {
                        exitOnError { parseConfigFromCli().check(xcfa, logger) }
                    }

                    Strategy.SERVER -> {
                        val safetyResultSupplier = parseConfigFromCli().checkInProcess(xcfa, solverHome, false, input!!.absolutePath, logger)
                        try {
                            safetyResultSupplier()
                        } catch (e: TimeoutException) {
                            exitProcess(ExitCodes.TIMEOUT.code)
                        } catch (e: ErrorCodeException) {
                            exitProcess(e.code)
                        }
                    }

                    Strategy.PORTFOLIO -> {
                        val portfolioDescriptor = File(portfolio.name.lowercase() + ".kts")
                        val kotlinEngine: ScriptEngine = ScriptEngineManager().getEngineByExtension("kts")
                        try {
                            val bindings: Bindings = SimpleBindings()
                            bindings["xcfa"] = xcfa
                            bindings["cFileName"] = input!!.absolutePath
                            bindings["logger"] = logger
                            bindings["smtHome"] = solverHome
                            bindings["bvType"] = BitwiseChecker.getBitwiseOption()
                            val portfolioResult = kotlinEngine.eval(FileReader(portfolioDescriptor), bindings) as Pair<XcfaCegarConfig, SafetyResult<*, *>>

                            concretizerSolver = portfolioResult.first.refinementSolver
                            validateConcretizerSolver = portfolioResult.first.validateRefinementSolver

                            portfolioResult.second
                        } catch (e: TimeoutException) {
                            exitProcess(ExitCodes.TIMEOUT.code)
                        } catch (e: ErrorCodeException) {
                            exitProcess(e.code)
                        } catch (e: Exception) {
                            logger.write(Logger.Level.RESULT, "Portfolio from $portfolioDescriptor could not be executed.")
                            e.printStackTrace()
                            exitProcess(ExitCodes.PORTFOLIO_ERROR.code)
                        }
                    }
                }
        if (svcomp || outputResults) {
            if (!svcomp) {
                resultFolder.mkdirs()

                val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
                val g: Graph = ArgVisualizer.getDefault().visualize(safetyResult.arg)
                argFile.writeText(GraphvizWriter.getInstance().writeString(g))

                if(safetyResult.isUnsafe) {
                    val traceFile = File(resultFolder, "trace.dot")
                    val traceG: Graph = TraceVisualizer.getDefault().visualize(safetyResult.asUnsafe().trace)
                    traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
                }

            } else {
                XcfaWitnessWriter().writeWitness(safetyResult, input!!, getSolver(concretizerSolver, validateConcretizerSolver))
            }
        }
        logger.write(Logger.Level.RESULT, safetyResult.toString() + "\n")
    }

    private fun parseConfigFromCli(): XcfaCegarConfig {
        val cegarConfig = XcfaCegarConfig()
        try {
            JCommander.newBuilder().addObject(cegarConfig).programName(JAR_NAME).build().parse(*remainingFlags.toTypedArray())
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