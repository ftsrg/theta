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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver

@JvmOverloads
fun buildBMC(
  monolithicExpr: MonolithicExpr,
  bmcSolver: Solver,
  logger: Logger,
  shouldGiveUp: (Int) -> Boolean = { false },
  bmcEnabled: () -> Boolean = { true },
  lfPathOnly: () -> Boolean = { true },
): BoundedChecker {
  return BoundedChecker(
    monolithicExpr,
    shouldGiveUp,
    bmcSolver,
    bmcEnabled,
    lfPathOnly,
    null,
    { false },
    null,
    { false },
    logger,
  )
}

@JvmOverloads
fun buildKIND(
  monolithicExpr: MonolithicExpr,
  bmcSolver: Solver,
  indSolver: Solver,
  logger: Logger,
  shouldGiveUp: (Int) -> Boolean = { false },
  bmcEnabled: () -> Boolean = { true },
  lfPathOnly: () -> Boolean = { true },
  kindEnabled: (Int) -> Boolean = { true },
): BoundedChecker {
  return BoundedChecker(
    monolithicExpr,
    shouldGiveUp,
    bmcSolver,
    bmcEnabled,
    lfPathOnly,
    null,
    { false },
    indSolver,
    kindEnabled,
    logger,
  )
}

@JvmOverloads
fun buildIMC(
  monolithicExpr: MonolithicExpr,
  bmcSolver: Solver,
  itpSolver: ItpSolver,
  logger: Logger,
  shouldGiveUp: (Int) -> Boolean = { false },
  bmcEnabled: () -> Boolean = { false },
  lfPathOnly: () -> Boolean = { true },
  imcEnabled: (Int) -> Boolean = { true },
): BoundedChecker {
  return BoundedChecker(
    monolithicExpr,
    shouldGiveUp,
    bmcSolver,
    bmcEnabled,
    lfPathOnly,
    itpSolver,
    imcEnabled,
    null,
    { false },
    logger,
  )
}
