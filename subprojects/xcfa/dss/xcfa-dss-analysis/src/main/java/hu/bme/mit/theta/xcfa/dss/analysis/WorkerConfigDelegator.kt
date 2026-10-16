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
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaLastPrecProvider
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XCFA

/**
 * The shape of `xcfa-cli`'s `getCegarChecker`, built only from lower-module types so this module
 * needn't depend on `xcfa-cli`. Any [SafetyChecker] fits, not just a CEGAR one.
 */
typealias XcfaChecker =
  SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>

/** Builds an [XcfaChecker] for an [XCFA]; named so rosters can hold a list of them. */
typealias CheckerFactory = (XCFA) -> XcfaChecker

/**
 * Serializes checker construction only: concurrent Z3 `Context` creation crashed natively, while
 * checks themselves run in parallel, each on its own fresh solver (see `doc/DSS.md`).
 */
private val solverConstructionLock = Any()

/**
 * Runs [construct] under the same lock as checker construction in [runWorkerConfig] - for anything
 * else in DSS that creates a native solver context (e.g. [DssPredicateOperators]).
 */
fun <T> withSolverConstructionLock(construct: () -> T): T =
  synchronized(solverConstructionLock) { construct() }

/**
 * [onLastPrec], if given, receives the precision the checker ended with - only from checkers that
 * report one ([XcfaLastPrecProvider], i.e. CEGAR), and only once the check is done.
 */
fun runWorkerConfig(
  xcfa: XCFA,
  checkerFactory: CheckerFactory,
  initialPrecision: XcfaPrec<*>? = null,
  onLastPrec: ((XcfaPrec<*>) -> Unit)? = null,
): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
  // Every solver the checker creates is closed once the check is done (and under the same lock as
  // construction): solver managers otherwise keep each one alive until SolverManager.closeAll(),
  // and DSS builds a fresh checker for every single block analysis.
  return SolverManager.withSolverScope(solverConstructionLock) {
    val checker = withSolverConstructionLock { checkerFactory(xcfa) }
    val result = if (initialPrecision != null) checker.check(initialPrecision) else checker.check()
    if (onLastPrec != null) (checker as? XcfaLastPrecProvider)?.lastPrec?.let(onLastPrec)
    result
  }
}
