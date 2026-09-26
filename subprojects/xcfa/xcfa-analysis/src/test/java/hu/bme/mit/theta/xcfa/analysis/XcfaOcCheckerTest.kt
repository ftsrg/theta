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
import hu.bme.mit.theta.xcfa.passes.LbePass
import hu.bme.mit.theta.xcfa.passes.RemoveDeadEnds
import hu.bme.mit.theta.xcfa.passes.UnusedVarPass
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

    /** Verdicts depending on the unroll exits and on cell-sensitive ordering constraints. */
    @JvmStatic
    fun unrollData(): Collection<Array<Any>> =
      listOf(OcDecisionProcedureType.IDL, OcDecisionProcedureType.BASIC).flatMap { dp ->
        listOf(
          arrayOf("/13loop_bound_safe.c", dp, SafetyResult<*, *>::isSafe),
          arrayOf("/14sequential_loops_unsafe.c", dp, SafetyResult<*, *>::isUnsafe),
          arrayOf("/15sequential_loops_safe.c", dp, SafetyResult<*, *>::isSafe),
          arrayOf("/20mutex_counter_unsafe.c", dp, SafetyResult<*, *>::isUnsafe),
        )
      }

    @JvmStatic
    fun dataRaceData(): Collection<Array<Any>> =
      listOf(
        arrayOf("/04multithread.c", SafetyResult<*, *>::isSafe),
        arrayOf("/05datarace.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/06ptrdatarace.c", SafetyResult<*, *>::isSafe),
        arrayOf("/07mutex.c", SafetyResult<*, *>::isSafe),
        arrayOf("/09atomicfield_norace.c", SafetyResult<*, *>::isSafe),
        arrayOf("/10plainfield_race.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/11atomicarray_norace.c", SafetyResult<*, *>::isSafe),
        arrayOf("/12pthread_array_race.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/16race_one_atomic.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/17norace_atomic_blocks.c", SafetyResult<*, *>::isSafe),
        arrayOf("/18race_after_loop.c", SafetyResult<*, *>::isUnsafe),
        arrayOf("/19norace_join.c", SafetyResult<*, *>::isSafe),
      )

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
    val parseContext = ParseContext()
    val xcfa = getXcfaFromC(stream!!, parseContext, false, property, NullLogger.getInstance()).first

    val ocChecker =
      XcfaOcChecker(
        xcfa = xcfa,
        property = property,
        parseContext = parseContext,
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

  private fun check(
    program: String,
    property: XcfaProperty,
    decisionProcedure: OcDecisionProcedureType,
  ): SafetyResult<*, *> {
    val stream = javaClass.getResourceAsStream(program)
    val parseContext = ParseContext()
    // As the CLI runs the OC checker: without LBE, which would merge the atomic units races are
    // detected between, and keeping every global access for a data race check.
    val lbeLevel = LbePass.defaultLevel
    val keepGlobalAccesses = UnusedVarPass.keepGlobalVariableAccesses
    val removeDeadEnds = RemoveDeadEnds.enabled
    LbePass.defaultLevel = LbePass.LbeLevel.NO_LBE
    if (property.inputProperty == ErrorDetection.DATA_RACE) {
      UnusedVarPass.keepGlobalVariableAccesses = true
      RemoveDeadEnds.enabled = false
    }
    val xcfa =
      try {
        getXcfaFromC(stream!!, parseContext, false, property, NullLogger.getInstance()).first
      } finally {
        LbePass.defaultLevel = lbeLevel
        UnusedVarPass.keepGlobalVariableAccesses = keepGlobalAccesses
        RemoveDeadEnds.enabled = removeDeadEnds
      }
    return XcfaOcChecker(
        xcfa = xcfa,
        property = property,
        parseContext = parseContext,
        decisionProcedure = decisionProcedure,
        smtSolver = "Z3:4.13",
        logger = NullLogger.getInstance(),
        conflictInput = null,
        outputConflictClauses = false,
        nonPermissiveValidation = false,
        autoConflictConfig = AutoConflictFinderConfig.NONE,
        autoConflictBound = -1,
        forceUnrollBoundEnd = -1,
      )
      .check(null)
  }

  @ParameterizedTest
  @MethodSource("unrollData")
  fun testUnrollExits(
    program: String,
    decisionProcedure: OcDecisionProcedureType,
    verdict: (SafetyResult<*, *>) -> Boolean,
  ) {
    println("Testing $program with $decisionProcedure...")
    Assertions.assertTrue(verdict(check(program, property, decisionProcedure)))
  }

  @ParameterizedTest
  @MethodSource("dataRaceData")
  fun testIdlDataRace(program: String, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing $program for data races with IDL...")
    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    Assertions.assertTrue(verdict(check(program, property, OcDecisionProcedureType.IDL)))
  }
}
