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
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseChecker
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseOption
import java.io.File
import java.io.FileInputStream
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import kotlin.system.exitProcess


class XcfaCli(private val args: Array<String>) {
    //////////// CONFIGURATION OPTIONS BEGIN ////////////
    //////////// input task ////////////
    @Parameter(names = ["--input"], description = "Path of the input C program", required = true)
    var input: File? = null

    //////////// backend options ////////////
    @Parameter(names = ["--backend"], description = "Backend analysis to use")
    var backend: Backend = Backend.CEGAR

    @Parameter(names = ["--strategy"], description = "Execution strategy")
    var strategy: Strategy = Strategy.PORTFOLIO

    @Parameter(names = ["--portfolio"], description = "Portfolio type (only valid with --strategy PORTFOLIO)")
    var portfolio: Portfolio = Portfolio.COMPLEX

    @Parameter(names = ["--timeout-ms"], description = "Timeout for verification (only valid with --strategy SERVER), use 0 for no timeout")
    var timeoutMs: Long = 0

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

    @Parameter(names = ["--output-results"], description = "Beside the input file creates a directory <input>-<timestamp>-result, in which it outputs the xcfa (simple and highlighted), cex, witness (graphml and dot) and statistics (txt)", help = true)
    var outputResults = false

    @Parameter(names = ["--witness-only"], description = "Does not output any other files, just a violation/correctness witness only")
    var witnessOnly = false


    /// Potential backends
    private val cegarConfig = XcfaCegarConfig()

    private fun run() {
        /// Checking flags
        try {
            JCommander.newBuilder().addObject(this).addObject(cegarConfig).programName(JAR_NAME).build().parse(*args)
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            println(ex.message)
            ex.usage()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        }
        /// version
        if (versionInfo) {
            CliUtils.printVersion(System.out)
            return
        }
        val logger = ConsoleLogger(logLevel)

        if(printConfigFile != null) {
            val file = File(printConfigFile!!)
            file.writeText(getGson().toJson(cegarConfig))
        }

        /// Starting frontend
        val swFrontend = Stopwatch.createStarted()
        val xcfa = try {
            val stream = FileInputStream(input!!)
            val xcfaFromC = getXcfaFromC(stream)
            logger.write(Logger.Level.INFO, "Frontend finished: ${xcfaFromC.name}  (in ${swFrontend.elapsed(TimeUnit.MILLISECONDS)} ms)\n")
            xcfaFromC
        } catch (e: Exception) {
            if(stacktrace) e.printStackTrace();
            System.err.println("Frontend failed!")
            exitProcess(ExitCodes.FRONTEND_FAILED.code)
        }
        swFrontend.reset().start()

        if(noAnalysis) {
            println("ParsingResult Success")
            return
        }

        val safetyResult: SafetyResult<*, *> =
                when (strategy) {
                    Strategy.DIRECT -> {
                        exitOnError { cegarConfig.check(xcfa, logger) }
                    }
                    Strategy.SERVER -> {
                        val safetyResultSupplier = cegarConfig.checkInProcess(xcfa, logger)
                        try {
                            safetyResultSupplier(timeoutMs)
                        } catch(e: TimeoutException) {
                            exitProcess(ExitCodes.TIMEOUT.code)
                        } catch(e: ErrorCodeException) {
                            exitProcess(e.code)
                        }
                    }
                    Strategy.PORTFOLIO -> {
                        // TODO: change this placeholder
                        val config1 = XcfaCegarConfig(
                                solverHome = cegarConfig.solverHome,
                                maxEnum= 1,
                                domain = Domain.EXPL,
                                refinement = Refinement.SEQ_ITP
                        )
                        val config2 = XcfaCegarConfig(
                                solverHome = cegarConfig.solverHome,
                                maxEnum= 1,
                                domain = Domain.PRED_CART,
                                refinement = Refinement.BW_BIN_ITP
                        )
                        val bvConfig = XcfaCegarConfig(
                                solverHome = cegarConfig.solverHome,
                                abstractionSolver = "mathsat:5.6.6",
                                refinementSolver = "mathsat:5.6.6",
                                maxEnum = 1,
                                domain = Domain.EXPL,
                                refinement = Refinement.SEQ_ITP
                        )
                        val fpConfig = XcfaCegarConfig(
                                solverHome = cegarConfig.solverHome,
                                abstractionSolver = "mathsat:fp",
                                validateAbstractionSolver = true,
                                refinementSolver = "mathsat:fp",
                                validateRefinementSolver = true,
                                maxEnum = 1,
                                domain = Domain.EXPL,
                                refinement = Refinement.SEQ_ITP
                        )

                        when(BitwiseChecker.getBitwiseOption()) {
                            BitwiseOption.INTEGER ->
                                try {
                                    config1.checkInProcess(xcfa, logger).invoke(60_000)
                                } catch(e1: Exception) {
                                    try {
                                        config2.checkInProcess(xcfa, logger).invoke(0)
                                    } catch (e2: Exception) {
                                        System.err.println("All configs failed.")
                                        e1.printStackTrace()
                                        System.err.println("====")
                                        e2.printStackTrace()
                                        exitProcess(ExitCodes.GENERIC_ERROR.code)
                                    }
                                }
                            BitwiseOption.BITWISE ->
                                try {
                                    bvConfig.checkInProcess(xcfa, logger).invoke(0)
                                } catch (e2: Exception) {
                                    System.err.println("All configs failed.")
                                    e2.printStackTrace()
                                    exitProcess(ExitCodes.GENERIC_ERROR.code)
                                }
                            BitwiseOption.BITWISE_FLOAT ->
                                try {
                                    fpConfig.checkInProcess(xcfa, logger).invoke(0)
                                } catch (e2: Exception) {
                                    System.err.println("All configs failed.")
                                    e2.printStackTrace()
                                    exitProcess(ExitCodes.GENERIC_ERROR.code)
                                }
                            else -> error("Unknown bv task type")
                        }
                    }
                }
        logger.write(Logger.Level.RESULT, safetyResult.toString() + "\n")
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