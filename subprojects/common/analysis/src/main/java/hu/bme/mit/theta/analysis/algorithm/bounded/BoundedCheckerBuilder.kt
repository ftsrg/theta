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

import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver

@JvmOverloads
fun <S : ExprState, A : ExprAction> buildBMC(
  monolithicExpr: MonolithicExpr,
  bmcSolver: Solver,
  valToState: (Valuation) -> S,
  biValToAction: (Valuation, Valuation) -> A,
  logger: Logger,
  shouldGiveUp: (Int) -> Boolean = { false },
  bmcEnabled: () -> Boolean = { true },
  lfPathOnly: () -> Boolean = { true },
): BoundedChecker<S, A> {
  return BoundedChecker(
    monolithicExpr,
    shouldGiveUp,
    bmcSolver,
    bmcEnabled,
    lfPathOnly,
    null,
		null,
    { false },
    null,
    { false },
    valToState,
    biValToAction,
    logger,
  )
}

@JvmOverloads
fun <S : ExprState, A : ExprAction> buildKIND(
  monolithicExpr: MonolithicExpr,
  bmcSolver: Solver,
  indSolver: Solver,
  valToState: (Valuation) -> S,
  biValToAction: (Valuation, Valuation) -> A,
  logger: Logger,
  shouldGiveUp: (Int) -> Boolean = { false },
  bmcEnabled: () -> Boolean = { true },
  lfPathOnly: () -> Boolean = { true },
  kindEnabled: (Int) -> Boolean = { true },
): BoundedChecker<S, A> {
  return BoundedChecker(
    monolithicExpr,
    shouldGiveUp,
    bmcSolver,
    bmcEnabled,
    lfPathOnly,
    null,
		null,
    { false },
    indSolver,
    kindEnabled,
    valToState,
    biValToAction,
    logger,
  )
}

@JvmOverloads
fun <S : ExprState, A : ExprAction> buildIMC(
  monolithicExpr: MonolithicExpr,
  bmcSolver: Solver,
  itpSolver: ItpSolver,
	imcFpSolver: Solver,
  valToState: (Valuation) -> S,
  biValToAction: (Valuation, Valuation) -> A,
  logger: Logger,
  shouldGiveUp: (Int) -> Boolean = { false },
  bmcEnabled: () -> Boolean = { true },
  lfPathOnly: () -> Boolean = { true },
  imcEnabled: (Int) -> Boolean = { true },
): BoundedChecker<S, A> {
  return BoundedChecker(
    monolithicExpr,
    shouldGiveUp,
    bmcSolver,
    bmcEnabled,
    lfPathOnly,
    itpSolver,
		imcFpSolver,
    imcEnabled,
    null,
    { false },
    valToState,
    biValToAction,
    logger,
  )
}
