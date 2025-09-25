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
package hu.bme.mit.theta.analysis.algorithm.bounded.pipeline

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.unit.UnitPrec

/**
 * Wraps a monolithic expression pass and a safety checker into a safety checker. The main use case
 * is to provide a convinient way to use monolithic expression passes without a pipeline. For this
 * reason, should not be used with passes that may want to change the direction of a pipeline as
 * this wrapper will always try to return after a single check.
 */
class MEPassCheckWrapper<Pr : InvariantProof>(
  val model: MonolithicExpr,
  val pass: DirectionalMonolithicExprPass<Pr>,
  val checkerFactory: (MonolithicExpr) -> SafetyChecker<Pr, Trace<ExplState, ExprAction>, UnitPrec>,
) : SafetyChecker<Pr, Trace<ExplState, ExprAction>, UnitPrec> {

  override fun check(input: UnitPrec?) =
    pass
      .backward(checkerFactory(pass.forward(model).expressionResult!!).check(input))
      .safetyResult!!
}
