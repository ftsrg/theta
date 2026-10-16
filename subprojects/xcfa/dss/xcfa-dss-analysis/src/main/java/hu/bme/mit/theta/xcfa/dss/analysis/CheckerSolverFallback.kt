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
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaLastPrecProvider
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants

/**
 * [primary]'s checkers, but a check that throws (e.g. Z3 on nonlinear arithmetic) is redone with a
 * [fallback] checker; if that throws too, its failure propagates with the first one suppressed.
 */
fun withCheckerSolverFallback(
  primary: CheckerFactory,
  fallback: CheckerFactory,
  statistics: DssSolverStatistics,
): CheckerFactory = { xcfa ->
  val first = primary(xcfa)
  object : XcfaChecker, XcfaLastPrecProvider {
    private var ran: XcfaChecker = first

    override val lastPrec: XcfaPrec<*>?
      get() = (ran as? XcfaLastPrecProvider)?.lastPrec

    override fun check(
      input: XcfaPrec<*>?
    ): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
      val failure =
        try {
          return first.check(input)
        } catch (e: InterruptedException) {
          throw e
        } catch (e: Exception) {
          e
        }
      statistics.checkerFailed.incrementAndGet()
      return try {
        ran = withSolverConstructionLock { fallback(xcfa) }
        ran.check(input).also {
          statistics.checkerFallbackDecided.incrementAndGet()
          statistics.report()
        }
      } catch (e: InterruptedException) {
        throw e
      } catch (e: Exception) {
        statistics.checkerFallbackFailed.incrementAndGet()
        statistics.report()
        e.addSuppressed(failure)
        throw e
      }
    }
  }
}
