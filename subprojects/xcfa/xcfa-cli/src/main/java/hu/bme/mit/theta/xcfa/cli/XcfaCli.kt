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
import com.google.gson.Gson
import com.google.gson.GsonBuilder
import com.google.gson.reflect.TypeToken
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import hu.bme.mit.theta.grammar.gson.ArgAdapter
import hu.bme.mit.theta.grammar.gson.ExplStateAdapter
import hu.bme.mit.theta.grammar.gson.StringTypeAdapter
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.solver.validator.SolverValidatorWrapperFactory
import hu.bme.mit.theta.solver.z3.Z3SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.getPartialOrder
import hu.bme.mit.theta.xcfa.getSymbols
import hu.bme.mit.theta.xcfa.gson.XcfaLabelAdapter
import hu.bme.mit.theta.xcfa.gson.xcfaLocationAdapter
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.io.File
import java.io.FileInputStream
import java.nio.file.Path
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess


class XcfaCli(private val args: Array<String>) {
    //////////// CONFIGURATION OPTIONS BEGIN ////////////
    //////////// input task ////////////
    @Parameter(names = ["--input"], description = "Path of the input C program", required = true)
    var input: File? = null

    //////////// backend options ////////////
    @Parameter(names = ["--backend"], description = "Backend analysis to use")
    var backend: Backend = Backend.CEGAR

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
            return
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
            logger.write(Logger.Level.INFO, "Frontend finished: ${xcfaFromC.name}  (in ${swFrontend.elapsed(TimeUnit.MILLISECONDS)} ms)")
            xcfaFromC
        } catch (e: Exception) {
            if(stacktrace) e.printStackTrace();
            System.err.println("Frontend failed!")
            exitProcess(-80)
        }
        swFrontend.reset().start()

        if(noAnalysis) return
        val swBackend = Stopwatch.createStarted()

        val safetyResult = try {
            cegarConfig.check(xcfa, logger)
        } catch (e: Exception) {
            e.printStackTrace();
            System.err.println("Analysis failed!");
            exitProcess(-82);
        }

        logger.write(Logger.Level.INFO, "walltime: ${swBackend.elapsed(TimeUnit.MILLISECONDS)} ms")
        swBackend.reset().start()

        val argAdapter = ArgAdapter(safetyResult.arg)
        val gson = getGson(xcfa)
        val json = gson.toJson(argAdapter)
        logger.write(Logger.Level.INFO, "serialization: ${swBackend.elapsed(TimeUnit.MILLISECONDS)} ms")
        swBackend.reset()

        val type = object: TypeToken<ArgAdapter<XcfaState<ExplState>, XcfaAction>>() {}.type
        val parsedBack = gson.fromJson<ArgAdapter<XcfaState<ExplState>, XcfaAction>>(json, type)

        swFrontend.reset().start()
        logger.write(Logger.Level.INFO, "deserialization: ${swFrontend.elapsed(TimeUnit.MILLISECONDS)} ms")
        swFrontend.reset().start()
        val parsedBackArg = parsedBack.instantiate(getPartialOrder { s1, s2 -> s1.isLeq(s2) })
        logger.write(Logger.Level.INFO, "rebuilding: ${swFrontend.elapsed(TimeUnit.MILLISECONDS)} ms")
    }

    private fun getGson(xcfa: XCFA): Gson {
        val gsonBuilder = GsonBuilder()
        val (scope, env) = xcfa.getSymbols()
        gsonBuilder.registerTypeAdapter(XcfaLocation::class.java, StringTypeAdapter(xcfaLocationAdapter))
        gsonBuilder.registerTypeHierarchyAdapter(Stmt::class.java, StringTypeAdapter { StatementWrapper(it, scope).instantiate(env) })
        gsonBuilder.registerTypeHierarchyAdapter(Expr::class.java, StringTypeAdapter { ExpressionWrapper(scope, it).instantiate(env) })
        gsonBuilder.registerTypeHierarchyAdapter(VarIndexing::class.java, StringTypeAdapter { BasicVarIndexing.fromString(it, scope, env) })
        gsonBuilder.registerTypeHierarchyAdapter(ExplState::class.java, ExplStateAdapter(scope, env))
        gsonBuilder.registerTypeHierarchyAdapter(XcfaLabel::class.java, XcfaLabelAdapter(scope, env))
        return gsonBuilder.create()
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