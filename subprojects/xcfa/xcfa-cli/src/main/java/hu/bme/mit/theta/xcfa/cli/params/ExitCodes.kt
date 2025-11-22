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
package hu.bme.mit.theta.xcfa.cli.params

import com.microsoft.z3.Z3Exception
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.solver.UnknownSolverStatusException
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverException
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException
import hu.bme.mit.theta.solver.validator.SolverValidationException
import kotlin.system.exitProcess

enum class ExitCodes(val code: Int) {
  GENERIC_ERROR(1),
  OUT_OF_MEMORY(200),
  TIMEOUT(201),
  SERVER_ERROR(202),
  PORTFOLIO_ERROR(203),
  UNSUPPORTED_ELEMENT(209),
  FRONTEND_FAILED(210),
  INVALID_PARAM(211),
  VERIFICATION_STUCK(220),
  SOLVER_ERROR(221),
}

data class ErrorCodeException(val code: Int) : Exception()

fun exitProcess(debug: Boolean, e: Throwable, code: Int): Nothing {
  try {
    println(
      "Error: ${e.javaClass} ${e.message ?: "-"} (${e.stackTrace.toList().subList(0, 2).joinToString { it.className + "#" + it.methodName + ":" + it.lineNumber }})"
    )
  } catch (t: Throwable) {
    // ignore at this point..
  }
  if (debug) {
    throw ErrorCodeException(code)
  } else exitProcess(code)
}

private fun Throwable.printCauseAndTrace(stacktrace: Boolean) {
  if (stacktrace) printStackTrace()
  val location = stackTrace.first { it.className.startsWith("hu.bme.mit.theta") }.toString()
  System.err.println("Process failed! ($location, $this)")
}

fun <T> exitOnError(stacktrace: Boolean, throwDontExit: Boolean, body: () -> T): T {
  try {
    return body()
  } catch (e: ErrorCodeException) {
    e.printStackTrace()
    exitProcess(throwDontExit, e, e.code)
  } catch (e: UnsupportedFrontendElementException) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.UNSUPPORTED_ELEMENT.code)
  } catch (e: SmtLibSolverException) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
  } catch (e: JavaSMTSolverException) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
  } catch (e: SolverValidationException) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
  } catch (e: Z3Exception) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
  } catch (e: com.microsoft.z3legacy.Z3Exception) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
  } catch (e: ClassCastException) {
    e.printCauseAndTrace(stacktrace)
    if (e.message?.contains("com.microsoft.z3") == true)
      exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
    else exitProcess(throwDontExit, e, ExitCodes.GENERIC_ERROR.code)
  } catch (e: NotSolvableException) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.VERIFICATION_STUCK.code)
  } catch (e: OutOfMemoryError) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.OUT_OF_MEMORY.code)
  } catch (e: UnknownSolverStatusException) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
  } catch (e: RuntimeException) {
    e.printCauseAndTrace(stacktrace)
    if (e.message?.contains("Solver problem") == true || e.message?.contains("z3") == true) {
      exitProcess(throwDontExit, e, ExitCodes.SOLVER_ERROR.code)
    } else {
      exitProcess(throwDontExit, e, ExitCodes.SERVER_ERROR.code)
    }
  } catch (e: Exception) {
    e.printCauseAndTrace(stacktrace)
    exitProcess(throwDontExit, e, ExitCodes.GENERIC_ERROR.code)
  }
}
