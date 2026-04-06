/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.defaultLazy
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.versionOption
import com.github.ajalt.clikt.parameters.types.file
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.table.BasicTableWriter
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverManager
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import hu.bme.mit.theta.xsts.analysis.concretizer.XstsTraceConcretizerUtil
import hu.bme.mit.theta.xsts.cli.optiongroup.InputOptions
import hu.bme.mit.theta.xsts.cli.optiongroup.OutputOptions
import java.io.File
import java.io.PrintWriter
import kotlin.system.exitProcess

abstract class XstsCliBaseCommand(name: String? = null, val help: String = "") :
  CliktCommand(name = name) {

  override fun help(c: Context) = help

  override val printHelpOnEmptyArgs = true

  init {
    versionOption(javaClass.`package`.implementationVersion ?: "unknown")
  }

  protected val inputOptions by InputOptions()
  protected val outputOptions by OutputOptions()
  protected open val defaultSolver: String = "Z3"
  protected val solver: String by
    option(help = "The solver to use for the check").defaultLazy { defaultSolver }
  private val smtHome: File by option().file().default(SmtLibSolverManager.HOME.toFile())
  private val logPattern: String? by
    option("--log", help = "Log pattern for the new logger API (e.g., 'DEBUG|INFO|WARN')")
  private val grepPattern: String? by
    option("--grep", "-grep", help = "Log pattern for the new logger API")

  protected val writer = BasicTableWriter(System.out, ",", "\"", "\"")

  init {
    val pattern = grepPattern ?: logPattern
    if (pattern != null) {
      Logger.init(pattern)
    } else {
      Logger.initOld(outputOptions.logLevel)
    }
  }

  protected abstract fun doRun()

  final override fun run() {
    try {
      registerSolverManagers()
      doRun()
    } catch (e: Exception) {
      printError(e)
      exitProcess(1)
    }
  }

  fun printError(exception: Exception) {
    val message = exception.message ?: ""
    val exceptionName = exception.javaClass.simpleName
    if (outputOptions.benchmarkMode) {
      writer.cell("[EX] $exceptionName: $message")
      writer.newRow()
      return
    }
    Logger.result("%s occurred, message: %s%n", exceptionName, message)
    if (outputOptions.stacktrace) {
      Logger.result("Trace:%n%s%n", exception.stackTraceToString())
    } else {
      Logger.result("Use --stacktrace for stack trace%n")
    }
  }

  fun printCommonResult(status: SafetyResult<*, *>, xsts: XSTS, totalTimeMs: Long) {
    listOf(
        status.isSafe,
        totalTimeMs,
        if (status.isUnsafe) "${status.asUnsafe().cex?.length() ?: "N/A"}" else "",
        xsts.vars.size,
      )
      .forEach(writer::cell)
  }

  protected open fun printExtraBenchmarkCells(status: SafetyResult<*, *>) {}

  protected fun printBenchmarkResult(status: SafetyResult<*, *>, xsts: XSTS, totalTimeMs: Long) {
    if (!outputOptions.benchmarkMode) {
      Logger.result(status.toString())
      return
    }
    printCommonResult(status, xsts, totalTimeMs)
    printExtraBenchmarkCells(status)
    writer.newRow()
  }

  private fun registerSolverManagers() {
    SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create())
    SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3legacy.Z3SolverManager.create())
    SolverManager.registerSolverManager(SmtLibSolverManager.create(smtHome.toPath()))
    SolverManager.registerSolverManager(JavaSMTSolverManager.create())
  }

  protected fun writeCex(status: SafetyResult<*, *>, xsts: XSTS) {
    if (outputOptions.cexfile == null || status.isSafe) return
    val trace = status.asUnsafe().cex as Trace<XstsState<*>, XstsAction>
    val concreteTrace =
      XstsTraceConcretizerUtil.concretize(trace, SolverManager.resolveSolverFactory(solver), xsts)
    val outputFile: File = outputOptions.cexfile!!
    outputFile.parentFile?.let { parent -> if (!parent.exists()) parent.mkdirs() }
    PrintWriter(outputFile).use { printWriter -> printWriter.write(concreteTrace.toString()) }
  }
}
