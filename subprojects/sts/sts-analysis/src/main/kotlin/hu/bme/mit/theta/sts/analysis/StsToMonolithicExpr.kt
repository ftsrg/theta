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
package hu.bme.mit.theta.sts.analysis

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.sts.STS

fun STS.toMonolithicExpr(): MonolithicExpr {
  return MonolithicExpr(this.init, this.trans, this.prop)
}

fun STS.valToAction(val1: Valuation, val2: Valuation): StsAction {
  return StsAction(this)
}

fun STS.valToState(val1: Valuation): ExplState {
  return ExplState.of(val1)
}
