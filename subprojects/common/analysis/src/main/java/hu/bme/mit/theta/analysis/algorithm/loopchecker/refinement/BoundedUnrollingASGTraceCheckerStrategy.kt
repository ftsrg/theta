/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.exception.TraceCheckingFailedException
import hu.bme.mit.theta.analysis.algorithm.loopchecker.util.VarCollectorStmtVisitor
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.ExprStates
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.ItpMarker
import hu.bme.mit.theta.solver.SolverFactory

class BoundedUnrollingASGTraceCheckerStrategy<S : ExprState, A : ExprAction>(
  private val trace: ASGTrace<S, A>,
  private val solverFactory: SolverFactory,
  init: Expr<BoolType>,
  private val bound: Int,
  private val logger: Logger,
) : AbstractASGTraceCheckerStrategy<S, A>(trace, solverFactory, init, logger) {

  override fun evaluateLoop(valuation: Valuation): ExprTraceStatus<ItpRefutation> {
    val indexingBeforeLoop = indexings[trace.tail.size]
    val indexingAfterLoop = indexings[trace.length()]
    val deltaIndexing = indexingAfterLoop.sub(indexingBeforeLoop)
    val usedVariablesPrecision = ExplPrec.of(expandUsedVariables(emptySet()))
    val requiredLoops: Int = findSmallestAbstractState(0, bound + 1, usedVariablesPrecision)
    if (requiredLoops == bound + 1) {
      throw TraceCheckingFailedException("Required number of unrolling is above $bound")
    }
    logger.write(Logger.Level.INFO, "Unrolling loop of trace at most %d times%n", requiredLoops)
    // The solver still holds init, tail and the first loop iteration, so every unrolling continues
    // from a reachable honda state. Equal states at any two honda visits form a concrete lasso.
    val hondaIndexings = mutableListOf(indexingBeforeLoop)
    var loopIndexing = indexingBeforeLoop
    for (i in 1..requiredLoops) {
      if (i > 1) {
        solver.push()
        putLoopOnSolver(satMarker, loopIndexing)
        if (solver.check().isUnsat) {
          solver.pop()
          putLoopOnSolver(unreachableMarker, loopIndexing)
          logger.write(Logger.Level.INFO, "Unrolled loop of trace %d times%n", i)
          return infeasibleThroughInterpolant(trace.tail.size, loopIndexing)
        }
      }
      loopIndexing = loopIndexing.add(deltaIndexing)
      solver.push()
      solver.add(unreachableMarker, Or(hondaIndexings.map { sameState(it, loopIndexing) }))
      if (solver.check().isSat) {
        logger.write(Logger.Level.INFO, "Unrolled loop of trace %d times%n", i)
        return getItpRefutationFeasible()
      }
      solver.pop()
      hondaIndexings.add(loopIndexing)
    }
    // A deterministic loop feasible this often would have repeated a honda state, so the bound does
    // not hold here (e.g. due to nondeterminism): let the default strategy decide
    throw TraceCheckingFailedException("Loop did not close within $requiredLoops unrollings")
  }

  private fun sameState(first: VarIndexing, second: VarIndexing): Expr<BoolType> =
    And(variables.map { Eq(PathUtils.unfold(it.ref, first), PathUtils.unfold(it.ref, second)) })

  private fun findSmallestAbstractState(i: Int, bound: Int, usedVariablesPrecision: ExplPrec): Int {
    val loop = trace.loop
    if (i == loop.size) return bound
    val expr: Expr<BoolType> = loop[i].source!!.state.toExpr()
    val statesForExpr: Collection<ExplState> =
      ExprStates.createStatesForExpr(
        solverFactory.createSolver(),
        expr,
        0,
        usedVariablesPrecision::createState,
        VarIndexingFactory.indexing(0),
        bound,
      )
    val currentSize: DomainSize =
      statesForExpr
        .map { state ->
          val fixedVars = ExprUtils.getVars(state.toExpr())
          val filtVars = usedVariablesPrecision.vars.filterNot(fixedVars::contains)
          val types = filtVars.map(VarDecl<*>::getType)
          val sizes = types.map(Type::getDomainSize)
          val res = sizes.fold(DomainSize.ONE, DomainSize::multiply)
          res
        }
        .fold(DomainSize.ZERO, DomainSize::add)
    return if (currentSize.isInfinite || currentSize.isBiggerThan(bound.toLong()))
      findSmallestAbstractState(i + 1, bound, usedVariablesPrecision)
    else findSmallestAbstractState(i + 1, currentSize.finiteSize.toInt(), usedVariablesPrecision)
  }

  fun expandUsedVariables(usedVariables: Set<VarDecl<*>>): Set<VarDecl<*>> {
    val expanded =
      trace.loop.fold(usedVariables) { acc, edge ->
        if (edge.action is StmtAction)
          acc + VarCollectorStmtVisitor.visitAll(edge.action.getStmts(), acc)
        else acc
      }

    return if (expanded.size > usedVariables.size) expandUsedVariables(expanded) else usedVariables
  }

  private fun putLoopOnSolver(marker: ItpMarker, startIndexing: VarIndexing) {
    var loopIndexing = startIndexing
    for (ldgEdge in trace.loop) {
      solver.add(marker, PathUtils.unfold(ldgEdge.source!!.state.toExpr(), loopIndexing))
      val action = ldgEdge.action!!
      solver.add(marker, PathUtils.unfold(action.toExpr(), loopIndexing))
      loopIndexing = loopIndexing.add(action.nextIndexing())
    }
    solver.add(
      marker,
      PathUtils.unfold(trace.loop[trace.loop.size - 1].target.state.toExpr(), loopIndexing),
    )
  }
}
