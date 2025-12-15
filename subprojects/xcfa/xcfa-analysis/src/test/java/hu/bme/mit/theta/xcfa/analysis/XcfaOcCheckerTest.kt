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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.oc.AutoConflictFinderConfig
import hu.bme.mit.theta.xcfa.analysis.oc.OcDecisionProcedureType
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcChecker
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class XcfaOcCheckerTest {

  companion object {

    private val program = "/04multithread.c"
    private val verdict = SafetyResult<*, *>::isUnsafe
    private val property = XcfaProperty(ErrorDetection.ERROR_LOCATION)

    @JvmStatic
    fun data(): Collection<Array<Any?>> {
      return listOf(
        arrayOf(OcDecisionProcedureType.IDL, AutoConflictFinderConfig.NONE, null),
        arrayOf(OcDecisionProcedureType.PROPAGATOR, AutoConflictFinderConfig.SIMPLE, null),
        arrayOf(OcDecisionProcedureType.BASIC, AutoConflictFinderConfig.GENERIC, 3),
      )
    }

    @BeforeAll
    @JvmStatic
    fun registerSolver() {
      SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create())
    }
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testOcChecker(
    decisionProcedure: OcDecisionProcedureType,
    autoConflictFinderConfig: AutoConflictFinderConfig,
    autoConflictBound: Int?,
  ) {
    println(
      "Testing $program with ($decisionProcedure, $autoConflictFinderConfig${autoConflictBound.let{"($it)"}})..."
    )
    val stream = javaClass.getResourceAsStream(program)
    val xcfa =
      getXcfaFromC(stream!!, ParseContext(), false, property, NullLogger.getInstance()).first

    val ocChecker =
      XcfaOcChecker(
        xcfa = xcfa,
        property = property.verifiedProperty,
        decisionProcedure = decisionProcedure,
        smtSolver = "Z3:4.13",
        logger = NullLogger.getInstance(),
        conflictInput = null,
        outputConflictClauses = false,
        nonPermissiveValidation = false,
        autoConflictConfig = autoConflictFinderConfig,
        autoConflictBound = autoConflictBound ?: -1,
      )

    val safetyResult = ocChecker.check(null)
    Assertions.assertTrue(verdict(safetyResult))
  }
}
