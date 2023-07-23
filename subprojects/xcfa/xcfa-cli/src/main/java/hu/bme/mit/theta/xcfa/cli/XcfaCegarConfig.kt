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

import com.beust.jcommander.Parameter
import com.google.gson.reflect.TypeToken
import com.zaxxer.nuprocess.NuAbstractProcessHandler
import com.zaxxer.nuprocess.NuProcess
import com.zaxxer.nuprocess.NuProcessBuilder
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.runtimemonitor.CexMonitor
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.por.XcfaDporLts
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.BufferedReader
import java.io.File
import java.io.InputStreamReader
import java.io.PrintWriter
import java.net.Socket
import java.nio.ByteBuffer
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess


data class XcfaCegarConfig(
    @Parameter(names = ["--error-detection"],
        description = "What kinds of errors to check for (ERROR_LOCATION or DATA_RACE)")
    var errorDetectionType: ErrorDetection = ErrorDetection.ERROR_LOCATION,
    @Parameter(names = ["--abstraction-solver"], description = "Abstraction solver name")
    var abstractionSolver: String = "Z3",
    @Parameter(names = ["--validate-abstraction-solver"],
        description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateAbstractionSolver: Boolean = false,
    @Parameter(names = ["--domain"], description = "Abstraction domain")
    var domain: Domain = Domain.EXPL,
    @Parameter(names = ["--maxenum"],
        description = "How many successors to enumerate in a transition. Only relevant to the explicit domain. Use 0 for no limit.")
    var maxEnum: Int = 1,
    @Parameter(names = ["--search"], description = "Search strategy")
    var search: Search = Search.ERR,
    @Parameter(names = ["--initprec"], description = "Initial precision")
    var initPrec: InitPrec = InitPrec.EMPTY,
    @Parameter(names = ["--por-level"], description = "POR dependency level")
    var porLevel: POR = POR.NOPOR,
    @Parameter(names = ["--refinement-solver"], description = "Refinement solver name")
    var refinementSolver: String = "Z3",
    @Parameter(names = ["--validate-refinement-solver"],
        description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateRefinementSolver: Boolean = false,
    @Parameter(names = ["--refinement"], description = "Refinement strategy")
    var refinement: Refinement = Refinement.SEQ_ITP,
    @Parameter(names = ["--predsplit"],
        description = "Predicate splitting (for predicate abstraction)")
    var exprSplitter: ExprSplitterOptions = ExprSplitterOptions.WHOLE,
    @Parameter(names = ["--prunestrategy"],
        description = "Strategy for pruning the ARG after refinement")
    var pruneStrategy: PruneStrategy = PruneStrategy.LAZY,
    @Parameter(names = ["--cex-monitor"])
    var cexMonitor: CexMonitorOptions = CexMonitorOptions.DISABLE,
    @Parameter(names = ["--timeout-ms"],
        description = "Timeout for verification (only valid with --strategy SERVER), use 0 for no timeout")
    var timeoutMs: Long = 0,
    @Parameter(names = ["--arg-to-file"])
    var argToFile: Boolean = false
) {

    @Suppress("UNCHECKED_CAST")
    private fun getCegarChecker(xcfa: XCFA,
        logger: Logger): CegarChecker<ExprState, ExprAction, Prec> {
        val abstractionSolverFactory: SolverFactory = getSolver(abstractionSolver,
            validateAbstractionSolver)
        val refinementSolverFactory: SolverFactory = getSolver(refinementSolver,
            validateRefinementSolver)

        val ignoredVarRegistry = mutableMapOf<Decl<out Type>, MutableSet<ExprState>>()

        val lts = porLevel.getLts(xcfa, ignoredVarRegistry)
        val waitlist = if (porLevel.isDynamic) {
            (lts as XcfaDporLts).waitlist
        } else {
            PriorityWaitlist.create<ArgNode<out XcfaState<out ExprState>, XcfaAction>>(
                search.getComp(xcfa))
        }

        val abstractionSolverInstance = abstractionSolverFactory.createSolver()
        val corePartialOrd: PartialOrd<out XcfaState<out ExprState>> = domain.partialOrd(
            abstractionSolverInstance)
        val abstractor: Abstractor<ExprState, ExprAction, Prec> = domain.abstractor(
            xcfa,
            abstractionSolverInstance,
            maxEnum,
            waitlist,
            refinement.stopCriterion,
            logger,
            lts,
            errorDetectionType,
            if (porLevel.isDynamic) {
                XcfaDporLts.getPartialOrder(corePartialOrd)
            } else {
                corePartialOrd
            }
        ) as Abstractor<ExprState, ExprAction, Prec>

        val ref: ExprTraceChecker<Refutation> =
            refinement.refiner(refinementSolverFactory)
                as ExprTraceChecker<Refutation>
        val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
            domain.itpPrecRefiner(exprSplitter.exprSplitter)
                as PrecRefiner<ExprState, ExprAction, Prec, Refutation>
        val atomicNodePruner: NodePruner<ExprState, ExprAction> = domain.nodePruner as NodePruner<ExprState, ExprAction>
        val refiner: Refiner<ExprState, ExprAction, Prec> =
            if (refinement == Refinement.MULTI_SEQ)
                if (porLevel == POR.AASPOR)
                    MultiExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger,
                        atomicNodePruner)
                else
                    MultiExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger)
            else
                if (porLevel == POR.AASPOR)
                    SingleExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger,
                        atomicNodePruner)
                else
                    SingleExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger)

        /*
        // set up stopping analysis if it is stuck on same ARGs and precisions
        if (disableCexMonitor) {
            ArgCexCheckHandler.instance.setArgCexCheck(false, false, mitigation)
        } else {
            if(checkArg) {
                ArgCexCheckHandler.instance.setArgCexCheck(true, true, mitigation)
            } else {
                ArgCexCheckHandler.instance.setArgCexCheck(true, false, mitigation)
            }
        }
        */

        val cegarChecker = if (porLevel == POR.AASPOR)
            CegarChecker.create(
                abstractor,
                AasporRefiner.create(refiner, pruneStrategy, ignoredVarRegistry),
                logger
            )
        else
            CegarChecker.create(abstractor, refiner, logger)

        initializeMonitors(cegarChecker, logger)

        return cegarChecker
    }

    private fun initializeMonitors(cc: CegarChecker<ExprState, ExprAction, Prec>, logger: Logger) {
        if (cexMonitor != CexMonitorOptions.DISABLE) {
            val cm = if (cexMonitor == CexMonitorOptions.MITIGATE) {
                throw RuntimeException(
                    "Mitigation is temporarily unusable, use DISABLE or CHECK instead")
                // CexMonitor(true, logger, cc.arg)
            } else { // CHECK
                CexMonitor(false, logger, cc.arg)
            }
            MonitorCheckpoint.register(cm, "CegarChecker.unsafeARG")
        }
    }

    fun check(xcfa: XCFA, logger: Logger): SafetyResult<ExprState, ExprAction> =
        try {
            val check = getCegarChecker(xcfa, logger).check(domain.initPrec(xcfa, initPrec))
            if (argToFile) {
                val fileName = "wdl-output.json"
                WebDebuggerLogger.getInstance().writeToFile(fileName)
            }
            check
        } catch (e: Exception) {
            if (argToFile) {
                val fileName = "wdl-output.json"
                WebDebuggerLogger.getInstance().writeToFile(fileName)
            }
            throw e
        }

    fun checkInProcessDebug(xcfa: XCFA, smtHome: String, writeWitness: Boolean,
        sourceFileName: String, logger: Logger, parseContext: ParseContext): () -> SafetyResult<*, *> {
        val gson = getGson(xcfa, { domain },
            { getSolver(abstractionSolver, validateAbstractionSolver).createSolver() })
        XcfaCegarServer.main(arrayOf("--smt-home",
            smtHome,
            "--return-safety-result",
            "" + !writeWitness,
            "--input",
            sourceFileName,
            "--config",
            gson.toJson(this),
            "--xcfa",
            gson.toJson(xcfa),
            "--parse-context",
            gson.toJson(parseContext),
            "--debug"
        ))
        error("Done debugging")
    }

    private fun getJavaExecutable(): String =
        ProcessHandle.current().info().command().orElse("java")

    fun checkInProcess(xcfa: XCFA, smtHome: String, writeWitness: Boolean, sourceFileName: String,
        logger: Logger, parseContext: ParseContext): () -> SafetyResult<*, *> {
        val pb = NuProcessBuilder(listOf(
            getJavaExecutable(),
            "-cp",
            File(
                XcfaCegarServer::class.java.protectionDomain.codeSource.location.toURI()).absolutePath,
            XcfaCegarServer::class.qualifiedName,
            "--smt-home",
            smtHome,
            "--return-safety-result",
            "" + !writeWitness,
            "--input",
            sourceFileName
        ))
        val processHandler = ProcessHandler(logger)
        pb.setProcessListener(processHandler)
        val process: NuProcess = pb.start()
        pb.environment().putAll(System.getenv())
        return {
            var connected = false
            var clientSocket: Socket? = null
            while (!connected) {
                try {
                    clientSocket = Socket("127.0.0.1", processHandler.port)
                    connected = true
                    logger.write(Logger.Level.VERBOSE, "Connected!\n")
                } catch (e: Exception) {
                    Thread.sleep(100)
                    logger.write(Logger.Level.VERBOSE,
                        "Connection failed (using port ${processHandler.port}), retrying...\n")
                }
            }
            checkNotNull(clientSocket)

            var safetyString: String?

            val gson = getGson(xcfa, { domain },
                { getSolver(abstractionSolver, validateAbstractionSolver).createSolver() })
            clientSocket.use {
                val writer = PrintWriter(clientSocket.getOutputStream(), true)
                val reader = BufferedReader(InputStreamReader(clientSocket.getInputStream()))
                writer.println(gson.toJson(this))
                writer.println(gson.toJson(xcfa))
                writer.println(gson.toJson(parseContext))
                val retCode = process.waitFor(timeoutMs, TimeUnit.MILLISECONDS)
                if (retCode == Int.MIN_VALUE) {
                    if (!processHandler.writingSafetyResult) {
                        process.destroy(true)
                        throw ErrorCodeException(ExitCodes.TIMEOUT.code)
                    } else {
                        logger.write(Logger.Level.RESULT,
                            "Config timed out but started writing result: $this")
                        val retCode = process.waitFor(0, TimeUnit.MILLISECONDS)
                        if (retCode != 0) {
                            throw ErrorCodeException(retCode)
                        }
                    }
                } else if (retCode != 0) {
                    throw ErrorCodeException(retCode)
                }

                if (writeWitness) {
                    logger.write(Logger.Level.RESULT, "Config successful, exiting: $this")
                    exitProcess(0)
                } else {
                    logger.write(Logger.Level.RESULT,
                        "Config successful, reading back result: $this")
                    safetyString = reader.readLine()
                }
            }
            val type =
                if (domain == Domain.EXPL)
                    object : TypeToken<SafetyResult<XcfaState<ExplState>, XcfaAction>>() {}.type
                else if (domain == Domain.PRED_BOOL || domain == Domain.PRED_CART || domain == Domain.PRED_SPLIT)
                    object : TypeToken<SafetyResult<XcfaState<PredState>, XcfaAction>>() {}.type
                else
                    error("Domain $domain is not implemented in the GSON parser.")
            try {
                gson.fromJson(safetyString, type)
            } catch (e: Exception) {
                val tempFile = File.createTempFile("safetyresult", ".json")
                tempFile.writeText(safetyString!!)
                e.printStackTrace()
                error("Erroneous SafetyResult, see file ${tempFile.absolutePath}")
            }
        }
    }
}

private class ProcessHandler(
    private val logger: Logger,
) : NuAbstractProcessHandler() {

    private var stdoutBuffer = ""
    internal var writingSafetyResult = false
    var port: Int = -1
    override fun onStdout(buffer: ByteBuffer, closed: Boolean) {
        if (!closed) {
            val bytes = ByteArray(buffer.remaining())
            buffer[bytes]
            val str = bytes.decodeToString()
            if (port == -1) {
                val portMatch = Regex("Port=\\(([0-9]*)\\)").find(str)
                if (portMatch != null) {
                    if (portMatch.groupValues.size == 2) {
                        port = Integer.parseInt(portMatch.groupValues[1])
                    }
                }
            }
            stdoutBuffer += str
            val matchResults = Regex("([a-zA-Z]*)\t\\{([^}]*)}").findAll(stdoutBuffer)
            var length = 0
            for (matchResult in matchResults) {
                val (level, message) = matchResult.destructured
                val logLevel = try {
                    Logger.Level.valueOf(level)
                } catch (_: Exception) {
                    Logger.Level.VERBOSE
                }
                logger.write(logLevel, message)
                if (message.contains("(SafetyResult")) writingSafetyResult = true
                length += matchResult.range.count()
            }
            stdoutBuffer = stdoutBuffer.substring(length)
        }
    }

    override fun onStderr(buffer: ByteBuffer, closed: Boolean) {
        if (!closed) {
            val bytes = ByteArray(buffer.remaining())
            buffer.get(bytes)
            System.err.print(bytes.decodeToString())
        }
    }
}