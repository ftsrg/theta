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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException
import hu.bme.mit.theta.xcfa.cli.params.ErrorCodeException
import hu.bme.mit.theta.xcfa.cli.params.ExitCodes
import hu.bme.mit.theta.xcfa.cli.params.exitOnError
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test

class ExitCodesTest {

  private fun codeOf(e: Throwable): Int =
    assertThrows(ErrorCodeException::class.java) { exitOnError(false, true) { throw e } }.code

  private fun thrownAt(className: String, e: RuntimeException) =
    e.apply { stackTrace = arrayOf(StackTraceElement(className, "m", null, 1)) }

  @Test
  fun `a wrapped solver exception is a solver error`() {
    val e = RuntimeException(SmtLibSolverException("Model does not have a value"))
    assertEquals(ExitCodes.SOLVER_ERROR.code, codeOf(e))
  }

  @Test
  fun `an exception thrown inside a solver integration is a solver error`() {
    val e = thrownAt("hu.bme.mit.theta.solver.z3.Z3TermTransformer", IllegalStateException())
    assertEquals(ExitCodes.SOLVER_ERROR.code, codeOf(e))
  }

  @Test
  fun `an exception thrown by the analysis is a server error`() {
    val e =
      thrownAt(
        "hu.bme.mit.theta.xcfa.analysis.XcfaAnalysisKt",
        IllegalStateException("No such method"),
      )
    assertEquals(ExitCodes.SERVER_ERROR.code, codeOf(e))
  }
}
