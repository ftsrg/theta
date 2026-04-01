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

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger.Level.INFO
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xcfa.analysis.coi.ConeOfInfluence
import hu.bme.mit.theta.xcfa.analysis.coi.XcfaCoiMultiThread
import hu.bme.mit.theta.xcfa.analysis.por.XcfaSporLts
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.util.concurrent.TimeUnit

class XcfaUnitAnalysisTest {

  companion object {
    @JvmStatic
    fun data(): Collection<Array<Any>> {
      return listOf(
        arrayOf("/00assignment.c", 8, SafetyResult<*, *>::isUnsafe),
        arrayOf("/00assignment.c", 2, this::isUnknown),
        arrayOf("/01function.c", 16, SafetyResult<*, *>::isUnsafe),
        arrayOf("/02functionparam.c", 16, SafetyResult<*, *>::isSafe),
        arrayOf("/03nondetfunction.c", 16, SafetyResult<*, *>::isUnsafe),
        arrayOf("/04multithread.c", 40, SafetyResult<*, *>::isUnsafe),
        arrayOf("/05assignment_safe.c", 16, SafetyResult<*, *>::isSafe),
        arrayOf("/05assignment_safe.c", 2, this::isUnknown),
        arrayOf("/06spuriousrace_untimed.c", 35, SafetyResult<*, *>::isUnsafe),
        arrayOf("/07spuriousrace_timed.c", 35, this::isUnknown),
      )
    }

    private fun isUnknown(safetyResult: SafetyResult<*, *>) =
      !safetyResult.isSafe && !safetyResult.isUnsafe
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testNoporBounded(filepath: String, bound: Int, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing NOPOR on $filepath...")
    val logger = ConsoleLogger(INFO)
    val stopwatch = Stopwatch.createStarted()
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
    ConeOfInfluence = XcfaCoiMultiThread(xcfa)

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val checker = getBoundedXcfaChecker(xcfa, ErrorDetection.ERROR_LOCATION, bound, solver)
    val safetyResult = checker.check()

    logger.write(
      INFO,
      "$filepath finished in ${stopwatch.elapsed(TimeUnit.MILLISECONDS)} ms\n",
    )
    Assertions.assertTrue(verdict(safetyResult))
  }

  @ParameterizedTest
  @MethodSource("data")
  fun testSporBounded(filepath: String, bound: Int, verdict: (SafetyResult<*, *>) -> Boolean) {
    println("Testing SPOR on $filepath...")
    val logger = ConsoleLogger(INFO)
    val stopwatch = Stopwatch.createStarted()
    val stream = javaClass.getResourceAsStream(filepath)
    val xcfa = getXcfaFromC(stream!!, ParseContext(), false, false, NullLogger.getInstance()).first
    ConeOfInfluence = XcfaCoiMultiThread(xcfa)
    val lts = XcfaSporLts(xcfa)

    val solver = Z3LegacySolverFactory.getInstance().createSolver()
    val checker = getBoundedXcfaChecker(xcfa, lts, ErrorDetection.ERROR_LOCATION, bound, solver)
    val safetyResult = checker.check()

    logger.write(
      INFO,
      "$filepath finished in ${stopwatch.elapsed(TimeUnit.MILLISECONDS)} ms\n",
    )
    Assertions.assertTrue(verdict(safetyResult))
  }
}
