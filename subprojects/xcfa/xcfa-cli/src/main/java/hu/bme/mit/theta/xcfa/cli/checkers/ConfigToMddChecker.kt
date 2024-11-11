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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.bounded.createAbstract
import hu.bme.mit.theta.analysis.algorithm.bounded.createReversed
import hu.bme.mit.theta.analysis.algorithm.mdd.MddCex
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.MddProof
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.orderVarsFromRandomStartingPoints
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.XCFA

fun getMddChecker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<MddProof, MddCex, Void> {
  val mddConfig = config.backendConfig.specConfig as MddConfig

  val refinementSolverFactory: SolverFactory = getSolver(mddConfig.solver, mddConfig.validateSolver)

  val monolithicExpr =
    xcfa
      .toMonolithicExpr(parseContext, initValues = true)
      .let { if (mddConfig.reversed) it.createReversed() else it }
      .let {
        if (mddConfig.cegar) it.createAbstract(mddConfig.initPrec.predPrec(xcfa).p.innerPrec)
        else it
      }

  val initRel = monolithicExpr.initExpr
  val initIndexing = monolithicExpr.initOffsetIndex
  val transRel =
    object : ExprAction {
      override fun toExpr() = monolithicExpr.transExpr

      override fun nextIndexing() = monolithicExpr.transOffsetIndex
    }
  val safetyProperty = monolithicExpr.propExpr
  val stmts =
    xcfa.procedures
      .flatMap { it.edges.flatMap { xcfaEdge -> xcfaEdge.getFlatLabels().map { it.toStmt() } } }
      .toSet()
  val variableOrder = orderVarsFromRandomStartingPoints(monolithicExpr.vars, stmts, 20)
  val solverPool = SolverPool(refinementSolverFactory)
  val iterationStrategy = mddConfig.iterationStrategy

  return MddChecker.create(
    initRel,
    initIndexing,
    transRel,
    safetyProperty,
    variableOrder,
    solverPool,
    logger,
    iterationStrategy,
  )
}
