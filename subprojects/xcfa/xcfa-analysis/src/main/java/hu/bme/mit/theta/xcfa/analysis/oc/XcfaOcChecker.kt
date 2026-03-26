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

package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.algorithm.oc.Reason
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.solver.SolverStatus

/**
 * An OC checker for XCFA event graphs. It is technically a wrapper around core OC checker
 * implementations.
 */
internal interface XcfaOcChecker : OcChecker<XcfaEvent> {

  /** Returns the result status of the verification problem (SAT/UNSAT). */
  val status: SolverStatus?

  /**
   * Returns a model of the verification problem, that is an assignment to all variables in the
   * verification problem, if the result is SAT, otherwise null.
   */
  val model: Valuation?

  /** Add constraints to the underlying solver based on the given event graph. */
  fun initialize(eg: XcfaToEventGraph.EventGraph)

  /** Exclude the given conflict from the search space of the underlying solver. */
  fun addConflict(conflict: Reason)

  /** Print statistics of the verification process. */
  fun printStatistics(logger: Logger)
}
