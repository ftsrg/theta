/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.defaultLazy
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.versionOption
import com.github.ajalt.clikt.parameters.types.file
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger
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

abstract class XstsCliBaseCommand(name: String? = null, help: String = "") :
  CliktCommand(name = name, help = help, printHelpOnEmptyArgs = true) {

  init {
    versionOption(javaClass.`package`.implementationVersion ?: "unknown")
  }

  protected val inputOptions by InputOptions()
  protected val outputOptions by OutputOptions()
  protected open val defaultSolver: String = "Z3"
  protected val solver: String by
    option(help = "The solver to use for the check").defaultLazy { defaultSolver }
  private val smtHome: File by option().file().default(SmtLibSolverManager.HOME.toFile())
  protected val logger: Logger by lazy {
    if (outputOptions.benchmarkMode) NullLogger.getInstance()
    else ConsoleLogger(outputOptions.logLevel)
  }
  protected val writer = BasicTableWriter(System.out, ",", "\"", "\"")

  fun printError(exception: Exception) {
    val message = exception.message ?: ""
    val exceptionName = exception.javaClass.simpleName
    if (outputOptions.benchmarkMode) {
      writer.cell("[EX] $exceptionName: $message")
      writer.newRow()
      return
    }
    logger.write(Logger.Level.RESULT, "%s occurred, message: %s%n", exceptionName, message)
    if (outputOptions.stacktrace) {
      logger.write(Logger.Level.RESULT, "Trace:%n%s%n", exception.stackTraceToString())
    } else {
      logger.write(Logger.Level.RESULT, "Use --stacktrace for stack trace%n")
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

  fun registerSolverManagers() {
    SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create())
    SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3legacy.Z3SolverManager.create())
    SolverManager.registerSolverManager(SmtLibSolverManager.create(smtHome.toPath(), logger))
    SolverManager.registerSolverManager(JavaSMTSolverManager.create())
  }

  protected fun writeCex(status: SafetyResult<*, *>, xsts: XSTS) {
    if (outputOptions.cexfile == null || status.isSafe) return
    val trace = status.asUnsafe().cex as Trace<XstsState<*>, XstsAction>
    val concreteTrace =
      XstsTraceConcretizerUtil.concretize(trace, SolverManager.resolveSolverFactory(solver), xsts)
    val outputFile: File = outputOptions.cexfile!!
    outputFile.parentFile?.let { parent ->
      if (!parent.exists()) parent.mkdirs()
    }
    PrintWriter(outputFile).use { printWriter -> printWriter.write(concreteTrace.toString()) }
  }
}
