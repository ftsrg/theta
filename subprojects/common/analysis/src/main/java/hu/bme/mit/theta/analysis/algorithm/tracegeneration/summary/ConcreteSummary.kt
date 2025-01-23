/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.core.model.Valuation

class ConcreteSummary<S : State, A : Action>(
  val valuationMap: MutableMap<AbstractSummaryNode<out S, out A>, Valuation>,
  val summary: AbstractTraceSummary<out S, out A>,
) {
  // TODO check that every node has a valuation?

  fun getValuation(node: AbstractSummaryNode<S, A>): Valuation {
    return valuationMap[node]!!
  }
}
