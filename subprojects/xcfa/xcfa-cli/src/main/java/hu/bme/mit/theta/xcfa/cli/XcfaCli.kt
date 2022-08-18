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
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.Stmt
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


    //////////// abstraction options ////////////

    @Parameter(names = ["--domain"], description = "Abstraction domain")
    var domain: Domain = Domain.EXPL

    @Parameter(names = ["--abstraction-solver"], description = "Abstraction solver name")
    var abstractionSolver: String = "Z3"

    @Parameter(names = ["--validate-abstraction-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateAbstractionSolver = false

    @Parameter(names = ["--maxenum"], description = "How many successors to enumerate in a transition. Only relevant to the explicit domain. Use 0 for no limit.")
    var maxEnum: Int = 0

    @Parameter(names = ["--search"], description = "Search strategy")
    var search: Search = Search.ERR

    @Parameter(names = ["--initprec"], description = "Initial precision")
    var initPrec: InitPrec = InitPrec.EMPTY

    //////////// refiner options ////////////

    @Parameter(names = ["--refinement"], description = "Refinement strategy")
    var refinement: Refinement = Refinement.BW_BIN_ITP

    @Parameter(names = ["--refinement-solver"], description = "Refinement solver name")
    var refinementSolver: String = "Z3"

    @Parameter(names = ["--validate-refinement-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateRefinementSolver = false

    @Parameter(names = ["--predsplit"], description = "Predicate splitting (for predicate abstraction)")
    var exprSplitter: ExprSplitterOptions = ExprSplitterOptions.WHOLE

    @Parameter(names = ["--prunestrategy"], description = "Strategy for pruning the ARG after refinement")
    var pruneStrategy = PruneStrategy.LAZY


    //////////// SMTLib options ////////////
    @Parameter(names = ["--smt-home"], description = "The path of the solver registry")
    var home = SmtLibSolverManager.HOME.toAbsolutePath().toString()


    private fun run() {
        /// Checking flags
        try {
            JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(*args)
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

        // TODO later we might want to merge these two flags
//        if (witnessOnly) {
//            OutputHandler.create(OutputOptions.WITNESS_ONLY, input)
//        } else if (outputResults) {
//            OutputHandler.create(OutputOptions.OUTPUT_RESULTS, input)
//        } else {
//            OutputHandler.create(OutputOptions.NONE, input)
//        }
//        OutputHandler.getInstance().createResultsDirectory()

        val logger = ConsoleLogger(logLevel)

        /// Starting frontend
        val sw = Stopwatch.createStarted()
        val xcfa = try {
            val stream = FileInputStream(input!!)
            val xcfaFromC = getXcfaFromC(stream)
            println("Frontend finished: ${xcfaFromC.name}")
            xcfaFromC
        } catch (e: Exception) {
            if(stacktrace) e.printStackTrace();
            System.err.println("Frontend failed!")
            exitProcess(-80)
        }

//        OutputHandler.getInstance().writeXcfa(xcfa)
//        OutputHandler.getInstance().writeInputStatistics(xcfa)
        if(noAnalysis) return

//        val initTime = Duration.of(CpuTimeKeeper.getCurrentCpuTime(), ChronoUnit.SECONDS)
//        logger.write(Logger.Level.RESULT, "Time of model transformation: " + initTime.toMillis() + "ms" + System.lineSeparator());


        val cegarChecker = try{
            try {
                registerAllSolverManagers(home, logger)
            } catch (e: Exception) {
                e.printStackTrace()
                return
            }
            val abstractionSolverFactory: SolverFactory = getSolver(abstractionSolver, validateAbstractionSolver)
            val refinementSolverFactory: SolverFactory = getSolver(refinementSolver, validateRefinementSolver)

            val cegarConfig = XcfaCegarConfig(
                    abstractorConfig = AbstractorConfig(
                            abstractionSolverFactory = abstractionSolverFactory,
                            domain = domain,
                            maxEnum = maxEnum,
                            search = search,
                            initPrec = initPrec,
                            logger = logger
                    ),
                    refinerConfig = RefinerConfig(
                            refinementSolverFactory = refinementSolverFactory,
                            refinement = refinement,
                            exprSplitter = exprSplitter,
                            pruneStrategy = pruneStrategy,
                            logger = logger
                    ),
                    logger = logger
            )
            println("Configuration finished: $cegarConfig")
            cegarConfig.getCegarChecker(xcfa)
        } catch (e: Exception) {
            if(stacktrace) e.printStackTrace();
            System.err.println("Configuration failed!");
            exitProcess(-81);
        }

        val safetyResult = try {
            cegarChecker.check(domain.initPrec(xcfa, initPrec))
        } catch (e: Exception) {
            if(stacktrace) e.printStackTrace();
            System.err.println("Analysis failed!");
            exitProcess(-82);
        }

        val elapsed = sw.elapsed(TimeUnit.MILLISECONDS)
        sw.reset().start()
        println("walltime: $elapsed ms")

        val gson = getGson(xcfa)

        val argAdapter = ArgAdapter(safetyResult.arg)
        val json = gson.toJson(argAdapter)
        println("serialization: ${sw.elapsed(TimeUnit.MILLISECONDS)} ms")
        sw.reset().start()
        val type = object: TypeToken<ArgAdapter<XcfaState<ExplState>, XcfaAction>>() {}.type
        val parsedBack = gson.fromJson<ArgAdapter<XcfaState<ExplState>, XcfaAction>>(json, type)

        println("deserialization: ${sw.elapsed(TimeUnit.MILLISECONDS)} ms")
        sw.stop()

        check(argAdapter == parsedBack) {
            "Could not parse back the same ARG.\noriginal: \n$argAdapter\nparsed back: \n$parsedBack"
        }
        check(safetyResult.arg == parsedBack.instantiate(getPartialOrder { s1, s2 -> s1.isLeq(s2) })) { "Could not instantiate the same ARG." }

//        System.out.println("cputime: " + CpuTimeKeeper.getCurrentCpuTime() + " s")
    }

    private fun getGson(xcfa: XCFA): Gson {
        val gsonBuilder = GsonBuilder()
        val (scope, env) = xcfa.getSymbols()
        lateinit var gson: Gson
        gsonBuilder.registerTypeAdapter(XcfaLocation::class.java, StringTypeAdapter(xcfaLocationAdapter))
        gsonBuilder.registerTypeHierarchyAdapter(Stmt::class.java, StringTypeAdapter { StatementWrapper(it, scope).instantiate(env) })
        gsonBuilder.registerTypeHierarchyAdapter(ExplState::class.java, ExplStateAdapter(scope, env))
        gsonBuilder.registerTypeHierarchyAdapter(XcfaLabel::class.java, XcfaLabelAdapter(scope, env))
        gson = gsonBuilder.create()
        return gson
    }

    private fun getSolver(name: String, validate: Boolean) = if (validate) {
        SolverValidatorWrapperFactory.create(name)
    } else {
        SolverManager.resolveSolverFactory(name)
    }

    private fun registerAllSolverManagers(home: String, logger: Logger) {
//        CpuTimeKeeper.saveSolverTimes()
        SolverManager.closeAll()
        // register solver managers
        SolverManager.registerSolverManager(Z3SolverManager.create())
        if (OsHelper.getOs() == OsHelper.OperatingSystem.LINUX) {
            val homePath = Path.of(home)
            val smtLibSolverManager: SmtLibSolverManager = SmtLibSolverManager.create(homePath, logger)
            SolverManager.registerSolverManager(smtLibSolverManager)
        }
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