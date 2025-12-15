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

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.ErrorDetection.*
import java.util.function.Predicate

private typealias S = XcfaState<out PtrState<out ExprState>>

fun interface XcfaErrorDetector : Predicate<S> {

  fun exprTraceCheckerWrapper(
    exprTraceChecker: ExprTraceChecker<Refutation>
  ): ExprTraceChecker<Refutation> = exprTraceChecker
}

fun getXcfaErrorDetector(errorDetection: ErrorDetection): XcfaErrorDetector =
  when (errorDetection) { // TODO: when refactoring prop in xcfa, it has to be added here as well?
    NO_ERROR -> XcfaErrorDetector { false }
    ERROR_LOCATION -> XcfaErrorDetector { s -> s.processes.any { it.value.locs.peek().error } }
    DATA_RACE -> getDataRaceDetector()
    else ->
      error(
        "The error detection mode $errorDetection cannot be converted to a state predicate. Consider using a specification transformation."
      )
  }
