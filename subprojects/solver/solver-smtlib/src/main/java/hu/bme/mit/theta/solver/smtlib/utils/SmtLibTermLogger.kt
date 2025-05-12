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
package hu.bme.mit.theta.solver.smtlib.utils

import hu.bme.mit.theta.solver.*
import hu.bme.mit.theta.solver.logger.TermLogger
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibHornSolver
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.smtlib.impl.mathsat.MathSATSmtLibItpSolver
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibItpSolver
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary
import java.io.File

class SmtLibTermLogger(val filePrefix: String) : TermLogger {

  private val solver: () -> SmtLibSolver
  private val ucSolver: () -> SmtLibSolver
  private val itpSolver: () -> SmtLibItpSolver<*>
  private val hornSolver: () -> GenericSmtLibHornSolver
  private lateinit var cachedSolver: SmtLibSolver
  private lateinit var cachedUcSolver: SmtLibSolver
  private lateinit var cachedItpSolver: SmtLibItpSolver<*>
  private lateinit var cachedHornSolver: GenericSmtLibHornSolver

  private val loggerBinary: SmtLibSolverBinary

  private var idx = 0
  private var activeFile: File

  init {
    activeFile = File("$filePrefix${idx++}.smt2")
    activeFile.delete()

    val symbolTable = GenericSmtLibSymbolTable()
    val transformationManager = GenericSmtLibTransformationManager(symbolTable)
    val termTransformer = GenericSmtLibTermTransformer(symbolTable)
    loggerBinary = LoggerBinary()
    solver = {
      SmtLibSolver(symbolTable, transformationManager, termTransformer, loggerBinary, false)
    }
    ucSolver = {
      SmtLibSolver(symbolTable, transformationManager, termTransformer, loggerBinary, false)
    }
    itpSolver = {
      MathSATSmtLibItpSolver(symbolTable, transformationManager, termTransformer, loggerBinary)
    }
    hornSolver = {
      GenericSmtLibHornSolver(symbolTable, transformationManager, termTransformer, loggerBinary)
    }
  }

  private inner class LoggerBinary : SmtLibSolverBinary {

    override fun issueCommand(command: String) {
      activeFile.appendText(command)
      activeFile.appendText(System.lineSeparator())
    }

    override fun readResponse(): String {
      return "success"
    }

    override fun close() {}
  }

  override fun getSolver(): Solver =
    if (this::cachedSolver.isInitialized) cachedSolver else solver().also { cachedSolver = it }

  override fun getUCSolver(): UCSolver =
    if (this::cachedUcSolver.isInitialized) cachedUcSolver
    else ucSolver().also { cachedUcSolver = it }

  override fun getHornSolver(): HornSolver =
    if (this::cachedHornSolver.isInitialized) cachedHornSolver
    else hornSolver().also { cachedHornSolver = it }

  override fun getItpSolver(): ItpSolver =
    if (this::cachedItpSolver.isInitialized) cachedItpSolver
    else itpSolver().also { cachedItpSolver = it }

  override fun endCurrentFile() {
    activeFile = File("$filePrefix${idx++}.smt2")
    activeFile.delete()
  }
}
