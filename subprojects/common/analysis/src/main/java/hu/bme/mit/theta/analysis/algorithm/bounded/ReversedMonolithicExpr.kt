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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils

fun MonolithicExpr.createReversed(): MonolithicExpr {
  return MonolithicExpr(
    initExpr = Not(propExpr),
    transExpr = ExprUtils.reverse(transExpr, transOffsetIndex),
    propExpr = Not(initExpr),
    transOffsetIndex = transOffsetIndex,
    vars = vars,
    ctrlVars = ctrlVars,
    biValToAction = { valuation1, valuation2 ->
        val revAction = biValToAction(valuation2, valuation1)
        if (revAction is ReversibleAction) {
            revAction.reverse()
        } else {
            biValToAction(valuation1, valuation2)
        }
    }
  )
}
