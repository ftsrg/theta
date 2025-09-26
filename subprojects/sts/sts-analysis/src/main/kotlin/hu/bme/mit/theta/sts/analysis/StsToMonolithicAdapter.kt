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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.ProofConservingModelToMonolithicAdapter
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.sts.STS

class StsToMonolithicAdapter : ProofConservingModelToMonolithicAdapter<STS, ExplState, StsAction> {

  lateinit var sts: STS

  override fun modelToMonolithicExpr(model: STS): MonolithicExpr {
    sts = model
    return MonolithicExpr(model.init, model.trans, model.prop)
  }

  override fun traceToModelTrace(trace: Trace<ExplState, ExprAction>): Trace<ExplState, StsAction> =
    Trace.of(trace.states, trace.actions.map { _ -> StsAction(sts) })
}
