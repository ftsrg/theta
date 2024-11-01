/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement

import hu.bme.mit.theta.analysis.algorithm.loopchecker.LDGTrace
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.solver.Interpolant
import hu.bme.mit.theta.solver.SolverFactory

class MilanoLDGTraceCheckerStrategy<S : ExprState, A : ExprAction>(
  private val trace: LDGTrace<S, A>,
  solverFactory: SolverFactory,
  init: Expr<BoolType>,
  logger: Logger,
) : AbstractLDGTraceCheckerStrategy<S, A>(trace, solverFactory, init, logger) {

  override fun evaluateLoop(valuation: Valuation): ExprTraceStatus<ItpRefutation> {
    for (variable in variables) {
      solver.add(
        unreachableMarker,
        Eq(
          PathUtils.unfold(variable.ref, indexings[trace.tail.size]),
          PathUtils.unfold(variable.ref, indexings[stateCount - 1]),
        ),
      )
      if (solver.check().isSat) continue
      val interpolant: Interpolant = solver.getInterpolant(pattern)
      val interpolantExpr: Expr<BoolType> =
        ExprUtils.simplify(
          foldIn(interpolant.eval(satMarker), indexings[stateCount - 1], valuation)
        )
      logInterpolant(interpolantExpr)
      return ExprTraceStatus.infeasible(
        ItpRefutation.binary(interpolantExpr, stateCount - 1, stateCount)
      )
    }
    return getItpRefutationFeasible()
  }

  private fun <T : Type> foldIn(
    expr: Expr<T>,
    indexing: VarIndexing,
    valuation: Valuation,
  ): Expr<T> {
    if (expr is RefExpr<T>) {
      val decl = expr.decl
      if (decl is IndexedConstDecl<T>) {
        val varDecl = decl.varDecl
        val nPrimes = decl.index - indexing[varDecl]
        val varRef = varDecl.ref
        if (nPrimes == 0) return varRef
        if (nPrimes > 0) return Prime(varRef, nPrimes)
        return expr.eval(valuation)
      }
    }

    return expr.map { foldIn(it, indexing, valuation) }
  }
}
