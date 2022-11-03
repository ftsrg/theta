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

import com.beust.jcommander.Parameter
import com.google.gson.reflect.TypeToken
import com.zaxxer.nuprocess.NuAbstractProcessHandler
import com.zaxxer.nuprocess.NuProcess
import com.zaxxer.nuprocess.NuProcessBuilder
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.BufferedReader
import java.io.File
import java.io.InputStreamReader
import java.io.PrintWriter
import java.net.Socket
import java.nio.ByteBuffer
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException


data class XcfaCegarConfig(
        @Parameter(names = ["--abstraction-solver"], description = "Abstraction solver name")
        var abstractionSolver: String = "Z3",
        @Parameter(names = ["--validate-abstraction-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
        var validateAbstractionSolver: Boolean = false,
        @Parameter(names = ["--domain"], description = "Abstraction domain")
        var domain: Domain = Domain.EXPL,
        @Parameter(names = ["--maxenum"], description = "How many successors to enumerate in a transition. Only relevant to the explicit domain. Use 0 for no limit.")
        var maxEnum: Int = 0,
        @Parameter(names = ["--search"], description = "Search strategy")
        var search: Search = Search.ERR,
        @Parameter(names = ["--initprec"], description = "Initial precision")
        var initPrec: InitPrec = InitPrec.EMPTY,
        @Parameter(names = ["--refinement-solver"], description = "Refinement solver name")
        var refinementSolver: String = "Z3",
        @Parameter(names = ["--validate-refinement-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
        var validateRefinementSolver: Boolean = false,
        @Parameter(names = ["--refinement"], description = "Refinement strategy")
        var refinement: Refinement = Refinement.SEQ_ITP,
        @Parameter(names = ["--predsplit"], description = "Predicate splitting (for predicate abstraction)")
        var exprSplitter: ExprSplitterOptions = ExprSplitterOptions.WHOLE,
        @Parameter(names = ["--prunestrategy"], description = "Strategy for pruning the ARG after refinement")
        var pruneStrategy: PruneStrategy = PruneStrategy.LAZY,
        @Parameter(names = ["--no-cex-check"])
        var noCexCheck: Boolean = false,
        @Parameter(names = ["--timeout-ms"], description = "Timeout for verification (only valid with --strategy SERVER), use 0 for no timeout")
        var timeoutMs: Long = 0
) {
    @Suppress("UNCHECKED_CAST")
    private fun getCegarChecker(xcfa: XCFA, logger: Logger): CegarChecker<ExprState, ExprAction, Prec> {
        val abstractionSolverFactory: SolverFactory = getSolver(abstractionSolver, validateAbstractionSolver)
        val refinementSolverFactory: SolverFactory = getSolver(refinementSolver, validateRefinementSolver)

        val abstractor: Abstractor<ExprState, ExprAction, Prec> = domain.abstractor(
                xcfa,
                abstractionSolverFactory.createSolver(),
                maxEnum,
                search.getComp(xcfa),
                refinement.stopCriterion,
                logger
        ) as Abstractor<ExprState, ExprAction, Prec>

        val ref: ExprTraceChecker<Refutation> =
                refinement.refiner(refinementSolverFactory)
                        as ExprTraceChecker<Refutation>
        val precRefiner: PrecRefiner<ExprState, ExprAction, Prec, Refutation> =
                domain.itpPrecRefiner(exprSplitter.exprSplitter)
                        as PrecRefiner<ExprState, ExprAction, Prec, Refutation>
        val refiner: Refiner<ExprState, ExprAction, Prec> =
                if (refinement == Refinement.MULTI_SEQ)
                    MultiExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger)
                else
                    SingleExprTraceRefiner.create(ref, precRefiner, pruneStrategy, logger)

        // set up stopping analysis if it is stuck on same ARGs and precisions
        if (noCexCheck) {
            ArgCexCheckHandler.instance.setArgCexCheck(false, false)
        } else {
            ArgCexCheckHandler.instance.setArgCexCheck(true, refinement == Refinement.MULTI_SEQ)
        }

        return CegarChecker.create(abstractor, refiner, logger)
    }
    fun check(xcfa: XCFA, logger: Logger): SafetyResult<ExprState, ExprAction> =
            getCegarChecker(xcfa, logger).check(domain.initPrec(xcfa, initPrec))

    fun checkInProcess(xcfa: XCFA, smtHome: String, logger: Logger): () -> SafetyResult<*, *> {
        val pb = NuProcessBuilder(listOf(
                "java",
                "-cp",
                File(XcfaCegarServer::class.java.protectionDomain.codeSource.location.toURI()).absolutePath,
                XcfaCegarServer::class.qualifiedName,
                "--smt-home",
                smtHome
                ))
        val processHandler = ProcessHandler(logger)
        pb.setProcessListener(processHandler)
        val process: NuProcess = pb.start()
        pb.environment().putAll(System.getenv())
        return {
            var connected = false
            var clientSocket: Socket? = null
            while(!connected) {
                try {
                    clientSocket = Socket("127.0.0.1", processHandler.port)
                    connected = true
                    logger.write(Logger.Level.VERBOSE, "Connected!\n")
                } catch (e: Exception) {
                    Thread.sleep(100)
                    logger.write(Logger.Level.VERBOSE, "Connection failed (using port ${processHandler.port}), retrying...\n")
                }
            }
            checkNotNull(clientSocket)

            var safetyString: String?

            val gson = getGson(xcfa, {domain}, {getSolver(abstractionSolver, validateAbstractionSolver).createSolver()})
            clientSocket.use {
                val writer = PrintWriter(clientSocket.getOutputStream(), true)
                val reader = BufferedReader(InputStreamReader(clientSocket.getInputStream()))
                writer.println(gson.toJson(this))
                writer.println(gson.toJson(xcfa))
                val retCode = process.waitFor(timeoutMs, TimeUnit.MILLISECONDS)
                if(retCode == Int.MIN_VALUE) {
                    throw TimeoutException()
                } else if (retCode != 0) {
                    throw ErrorCodeException(retCode)
                }
                safetyString = reader.readLine()
            }
            val type =
                    if(domain == Domain.EXPL)
                        object: TypeToken<SafetyResult<XcfaState<ExplState>, XcfaAction>>() {}.type
                    else if (domain == Domain.PRED_BOOL || domain == Domain.PRED_CART || domain == Domain.PRED_SPLIT)
                        object: TypeToken<SafetyResult<XcfaState<PredState>, XcfaAction>>() {}.type
                    else
                        error("Domain ${domain} is not implemented in the GSON parser.")
            try{
                gson.fromJson(safetyString, type)
            } catch(e: Exception) {
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
    var port: Int = -1
    override fun onStdout(buffer: ByteBuffer, closed: Boolean) {
        if (!closed) {
            val bytes = ByteArray(buffer.remaining())
            buffer[bytes]
            val str = bytes.decodeToString()
            if(port == -1) {
                val portMatch = Regex("Port=\\(([0-9]*)\\)").find(str)
                if(portMatch != null) {
                    if(portMatch.groupValues.size == 2) {
                        port = Integer.parseInt(portMatch.groupValues[1])
                    }
                }
            }
            stdoutBuffer += str
            val matchResults = Regex("([a-zA-Z]*)\t\\{([^}]*)}").findAll(stdoutBuffer)
            var length = 0
            for(matchResult in matchResults) {
                val (level, message) = matchResult.destructured
                val logLevel = try{ Logger.Level.valueOf(level) } catch (_: Exception) { Logger.Level.VERBOSE }
                logger.write(logLevel, message)
                length+=matchResult.range.count()
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