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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XcfaLocation

/**
 * `packPost`: ORs the states a safe [result] reached at [location], a location of the checked XCFA
 * (for an extracted block, the clone in [BlockXcfaExtraction.locationMapping]); `False()` if none.
 */
fun packPostcondition(
  result: SafetyResult<LocationInvariants, *>,
  location: XcfaLocation,
): Expr<BoolType> {
  check(result.isSafe) { "Can only pack a postcondition out of a safe result, but got: $result" }
  val states = result.asSafe().proof.getPartitions()[location].orEmpty()
  val reachableExprs = states.map { it.toExpr() }.filterNot { it == False() }
  return if (reachableExprs.isEmpty()) False() else Or(reachableExprs)
}
