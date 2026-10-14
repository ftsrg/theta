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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.solver.UnknownSolverStatusException
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XCFA
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test

class CheckerSolverFallbackTest {

  private val xcfa = XCFA("empty", emptySet(), emptySet())
  private val result =
    SafetyResult.unknown<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>>()

  /** A factory of checkers that run [check]; counts the checkers built. */
  private class Stub(
    private val check:
      () -> SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>>
  ) {
    var built = 0
    val factory: CheckerFactory = {
      built++
      SafetyChecker { _: XcfaPrec<*>? -> check() }
    }
  }

  private val unknown = Stub { throw UnknownSolverStatusException() }
  private val crashing = Stub { throw IllegalStateException("native crash") }
  private val deciding = Stub { result }

  @Test
  fun `a check the solver fails on is repeated with the fallback`() {
    val statistics = DssSolverStatistics()
    val checker = withCheckerSolverFallback(unknown.factory, deciding.factory, statistics)(xcfa)
    assertSame(result, checker.check())
    assertEquals(1, statistics.checkerFailed.get())
    assertEquals(1, statistics.checkerFallbackDecided.get())
  }

  @Test
  fun `the fallback is not built when the solver decides`() {
    val statistics = DssSolverStatistics()
    withCheckerSolverFallback(deciding.factory, crashing.factory, statistics)(xcfa).check()
    assertEquals(0, crashing.built)
    assertEquals(0, statistics.checkerFailed.get())
  }

  @Test
  fun `a failure of the fallback propagates with the first failure suppressed`() {
    val statistics = DssSolverStatistics()
    val checker = withCheckerSolverFallback(unknown.factory, crashing.factory, statistics)(xcfa)
    val e = assertThrows(IllegalStateException::class.java) { checker.check() }
    assertEquals(UnknownSolverStatusException::class.java, e.suppressed.single().javaClass)
    assertEquals(1, statistics.checkerFallbackFailed.get())
  }
}
