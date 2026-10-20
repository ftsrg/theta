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
package hu.bme.mit.theta.xcfa.analysis.dss

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XCFA

/** A block checker; injected, since this module must not depend on `xcfa-cli`. */
typealias XcfaChecker =
  SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>

typealias CheckerFactory = (XCFA) -> XcfaChecker

/** Concurrent native solver construction crashed, so it is serialized; checks run in parallel. */
private val solverConstructionLock = Any()

fun <T> withSolverConstructionLock(construct: () -> T): T =
  synchronized(solverConstructionLock) { construct() }

fun runWorkerConfig(
  xcfa: XCFA,
  checkerFactory: CheckerFactory,
  initialPrecision: XcfaPrec<*>? = null,
): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
  // Solver managers keep every solver until closeAll(); DSS builds a checker per block analysis
  return SolverManager.withSolverScope(solverConstructionLock) {
    val checker = withSolverConstructionLock { checkerFactory(xcfa) }
    if (initialPrecision != null) checker.check(initialPrecision) else checker.check()
  }
}
