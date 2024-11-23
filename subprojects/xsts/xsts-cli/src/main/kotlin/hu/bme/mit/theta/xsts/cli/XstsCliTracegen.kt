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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.boolean
import com.github.ajalt.clikt.parameters.types.file
import com.google.common.base.Stopwatch
import com.google.common.io.Files
import com.google.common.io.MoreFiles
import com.google.common.io.RecursiveDeleteOption
import hu.bme.mit.theta.analysis.*
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.*
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.utils.AbstractTraceSummaryVisualizer
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsStateSequence
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsTraceGenerationConcretizerUtil
import hu.bme.mit.theta.xsts.analysis.tracegeneration.XstsTracegenBuilder
import hu.bme.mit.theta.xsts.analysis.tracegeneration.XstsTracegenConfig
import hu.bme.mit.theta.xsts.dsl.XstsDslManager
import java.io.*
import java.util.concurrent.TimeUnit
import kotlin.system.exitProcess

class XstsCliTracegen :
  XstsCliBaseCommand(
    name = "TRACEGEN",
    help = "Trace generation (instead of verification). Property and input options will be ignored",
  ) {
  val traceDir: File? by
    option(
        help =
          "Directory the traces should be written into. If not specified, output is written into model-directory/traces."
      )
      .file(mustExist = true, canBeFile = false) // use the non-null value in traceDirPath!
  val summary: Boolean by
    option(help = "If this flag is present, a concretized summary is generated.")
      .boolean()
      .default(false)
  val traces: Boolean by
    option(help = "If this flag is present, concretized traces are generated.")
      .boolean()
      .default(false)

  private fun toCexs(
    summaryStateMap:
      Map<AbstractSummaryNode<out XstsState<*>, out XstsAction>, XstsState<ExplState>>
  ): String {
    val sb = Utils.lispStringBuilder(javaClass.simpleName).body()

    for ((node, state) in summaryStateMap) {
      sb.add(
        Utils.lispStringBuilder(
            "_${node.id}: ${XstsState::class.java.simpleName}"
          ) // TODO number env separately
          .add(if (state.isInitialized) "post_init" else "pre_init")
          .add(if (state.lastActionWasEnv()) "last_env" else "last_internal")
          .body()
          .add(state.state.toString())
      )
    }

    for (node in summaryStateMap.keys) {
      for (outEdge in node.outEdges) {
        sb.add("${node.id} -> ${outEdge.target.id}")
      }
    }

    return sb.toString()
  }

  private fun printResult(
    concretizationResult:
      Map<AbstractSummaryNode<out XstsState<*>, out XstsAction>, XstsState<ExplState>>,
    abstractSummary: AbstractTraceSummary<out State, out Action>,
    totalTimeMs: Long,
    traceDirPath: File,
    xsts: XSTS,
  ) {
    logger.write(
      Logger.Level.RESULT,
      "Successfully generated a summary of ${abstractSummary.sourceTraces.size} traces in ${totalTimeMs}ms\n",
    )

    // TODO print coverage (full or not)?
    val graph = AbstractTraceSummaryVisualizer.visualize(abstractSummary)
    val visFile =
      traceDirPath.absolutePath +
        File.separator +
        inputOptions.model.name +
        ".abstract-trace-summary.png"
    GraphvizWriter.getInstance().writeFileAutoConvert(graph, visFile)
    logger.write(Logger.Level.SUBSTEP, "Abstract trace summary was visualized in ${visFile}\n")

    // trace concretization
    if (traces) {
      var traceCount = 0

      val concretizationResultTuple =
        XstsTraceGenerationConcretizerUtil.concretizeTraceList(
          traces as List<Trace<XstsState<ExplState>, XstsAction>>,
          Z3LegacySolverFactory.getInstance(),
          xsts,
        )
      val concretizedTraces: Set<XstsStateSequence> = concretizationResultTuple.get1()
      val report: String = concretizationResultTuple.get2()

      for (trace in concretizedTraces) {
        val traceFile =
          File(
            traceDirPath.absolutePath +
              File.separator +
              Files.getNameWithoutExtension(inputOptions.model.name) +
              "-" +
              traceCount +
              ".trace"
          )
        logger.write(Logger.Level.SUBSTEP, "Writing trace into file: %s%n", traceFile.path)
        PrintWriter(traceFile).use { printWriter -> printWriter.write(trace.toString()) }
        traceCount++

        logger.write(Logger.Level.SUBSTEP, "---------------------------%n")
      }
      val reportFile = File(traceDirPath.absolutePath + File.separator + "report.txt")
      logger.write(Logger.Level.MAINSTEP, "Writing report into file: %s%n", reportFile.path)

      PrintWriter(reportFile).use { printWriter -> printWriter.write(report) }
    }

    // summary concretization
    if (summary) {
      val concreteSummaryFile =
        traceDirPath.absolutePath + File.separator + inputOptions.model.name + ".cexs"
      val cexsString = toCexs(concretizationResult)
      PrintWriter(File(concreteSummaryFile)).use { printWriter -> printWriter.write(cexsString) }
      logger.write(
        Logger.Level.SUBSTEP,
        "Concrete trace summary exported to ${concreteSummaryFile}\n",
      )
    }
  }

  override fun run() {
    try {
      doRun()
    } catch (e: Exception) {
      printError(e)
      exitProcess(1)
    }
  }

  private fun doRun() {
    val traceDirPath: File =
      if (traceDir == null) {
        File(inputOptions.model.parent + File.separator + "traces")
      } else {
        traceDir!!
      }

    registerSolverManagers()
    val solverFactory = SolverManager.resolveSolverFactory(solver)

    val modelFile = inputOptions.model
    if (traceDirPath.exists()) {
      MoreFiles.deleteRecursively(traceDirPath.toPath(), RecursiveDeleteOption.ALLOW_INSECURE)
    }
    traceDirPath.mkdir()

    val propStream = ByteArrayInputStream(("prop {\n" + "\ttrue\n" + "}\n").toByteArray())
    val xsts =
      XstsDslManager.createXsts(SequenceInputStream(FileInputStream(modelFile), propStream))
    val sw = Stopwatch.createStarted()
    val checker: XstsTracegenConfig<out State, out Action, out Prec> =
      XstsTracegenBuilder(Z3SolverFactory.getInstance(), true)
        .logger(logger)
        .setGetFullTraces(false)
        .build(xsts)
    val result = checker.check()
    val summary = result.summary as AbstractTraceSummary<XstsState<*>, XstsAction>

    val concretizationResult =
      XstsTraceGenerationConcretizerUtil.concretizeSummary(
        summary,
        Z3LegacySolverFactory.getInstance(),
        xsts,
      )

    sw.stop()
    printResult(
      concretizationResult,
      result.summary,
      sw.elapsed(TimeUnit.MILLISECONDS),
      traceDirPath,
      xsts,
    )
  }
}
