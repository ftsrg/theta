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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExprCegarChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.createMonolithicL2S
import hu.bme.mit.theta.analysis.algorithm.bounded.createReversed
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.hu.bme.mit.theta.xsts.analysis.toMonolithicExpr

abstract class XstsCliMonolithicBaseCommand(name: String? = null, help: String = "") :
  XstsCliBaseCommand(name = name, help = help) {

  protected val reversed: Boolean by option(help = "Reversed state space exploration").flag()
  protected val livenessToSafety: Boolean by
    option(help = "Use liveness to safety transformation").flag()
  protected val cegar: Boolean by option(help = "Wrap analysis in CEGAR loop").flag()

  fun createMonolithicExpr(xsts: XSTS): MonolithicExpr {
    var monolithicExpr = xsts.toMonolithicExpr()
    if (livenessToSafety) {
      monolithicExpr = monolithicExpr.createMonolithicL2S()
    }
    if (reversed) {
      monolithicExpr = monolithicExpr.createReversed()
    }
    return monolithicExpr
  }

  fun <W : Proof> wrapInCegarIfNeeded(
    monolithicExpr: MonolithicExpr,
    solverFactory: SolverFactory,
    builder:
      (MonolithicExpr) -> SafetyChecker<W, out Trace<out ExprState, out ExprAction>, UnitPrec>,
  ): SafetyChecker<*, *, *> =
    if (cegar) {
      MonolithicExprCegarChecker(monolithicExpr, builder, logger, solverFactory)
    } else {
      builder(monolithicExpr)
    }
}
