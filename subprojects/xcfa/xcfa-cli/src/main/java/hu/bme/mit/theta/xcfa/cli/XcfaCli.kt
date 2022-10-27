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
    var strategy: Strategy = Strategy.SERVER

    //////////// debug options ////////////
    @Parameter(names = ["--stacktrace"], description = "Print full stack trace in case of exception")
    var stacktrace: Boolean = false

    //////////// output data and statistics ////////////
    @Parameter(names = ["--version"], description = "Display version", help = true)
    var versionInfo = false

    @Parameter(names = ["--loglevel"], description = "Detailedness of logging")
    var logLevel = Logger.Level.MAINSTEP

    @Parameter(names = ["--output-results"], description = "Beside the input file creates a directory <input>-<timestamp>-result, in which it outputs the xcfa (simple and highlighted), cex, witness (graphml and dot) and statistics (txt)", help = true)
    var outputResults = false

    @Parameter(names = ["--witness-only"], description = "Does not output any other files, just a violation/correctness witness only")
    var witnessOnly = false

    @Parameter(names = ["--no-analysis"], description = "Executes the model transformation to XCFA and CFA, and then exits; use with --output-results to get data about the (X)CFA")
    var noAnalysis = false

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
                            safetyResultSupplier(900_000)
                        } catch(e: TimeoutException) {
                            exitProcess(ExitCodes.TIMEOUT.code)
                        } catch(e: ErrorCodeException) {
                            exitProcess(e.code)
                        }
                    }
                    else -> {
                        TODO()
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