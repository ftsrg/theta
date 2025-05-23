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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.bounded.*
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.LassoCheckerConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.LinkedList

fun getLassoChecker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
): SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

  val lassoConfig = config.backendConfig.specConfig as LassoCheckerConfig
  val solverFactory: SolverFactory = getSolver(lassoConfig.solver, lassoConfig.validateSolver)

  val proc = xcfa.initProcedures.first().first

  val selfLoops =
    proc.edges
      .filter { it.target == it.source }
      .map {
        var indexing: VarIndexing = VarIndexingFactory.basicVarIndexing(0)
        val assumptions = LinkedList<Expr<BoolType>>()
        val elze = LinkedList<Expr<BoolType>>()
        for (label in it.getFlatLabels()) {
          label as StmtLabel

          val result = StmtUtils.toExpr(label.stmt, indexing)
          val expr = PathUtils.unfold(And(result.exprs), indexing)
          indexing = result.indexing

          if (label.stmt is AssumeStmt) {
            assumptions.add(expr)
          }
          elze.add(expr)
        }

        val recCondition = And(assumptions)
        val transferRel = And(elze)
        val stem = getNondetPath(proc.initLoc, it.source)

        val stemExpr =
          PathUtils.unfold(
            And(
              StmtUtils.toExpr(
                  SequenceStmt.of(listOf(stem, Assume(recCondition))),
                  VarIndexingFactory.basicVarIndexing(0),
                )
                .exprs
            ),
            VarIndexingFactory.basicVarIndexing(0),
          )
        LassoExprs(stemExpr, recCondition, transferRel)
      }

  return SafetyChecker<
    EmptyProof,
    Trace<XcfaState<PtrState<ExplState>>, XcfaAction>,
    XcfaPrec<PtrPrec<ExplPrec>>,
  > {
    val solver = solverFactory.createSolver()
    for ((stem, rec, trans) in selfLoops) {
      val success =
        WithPushPop(solver).use {
          logger.writeln(Logger.Level.INFO, "Checking recurrence location reachability..")
          solver.add(stem)
          solver.check()
          if (solver.status.isUnsat) {
            logger.writeln(Logger.Level.INFO, "Recurrence location reachability failed.")
            false
          } else {
            logger.writeln(Logger.Level.INFO, "Recurrence location reachability successful.")
            true
          }
        }
      if (success) {
        WithPushPop(solver).use {
          logger.writeln(Logger.Level.INFO, "Checking recurrence set re-reachability..")
          val consts =
            ExprUtils.getIndexedConstants(trans).associateWith {
              Param(it.varDecl.name, it.varDecl.type)
            }
          val forall =
            ExprUtils.simplify(
              Forall(
                consts.values,
                Imply(ExprUtils.changeDecls(rec, consts), ExprUtils.changeDecls(trans, consts)),
              )
            )
          solver.add(forall)
          solver.check()
          if (solver.status.isUnsat) {
            logger.writeln(Logger.Level.INFO, "Recurrence set re-reachability failed.")
            val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())
            solver.assertions.forEach { logger.writeln(Logger.Level.INFO, manager.toTerm(it)) }
            return@SafetyChecker SafetyResult.safe(EmptyProof.getInstance())
          } else {
            logger.writeln(Logger.Level.INFO, "Recurrence set re-reachability successful.")
            return@SafetyChecker SafetyResult.unsafe(
              Trace.of(listOf(XcfaState(xcfa, proc.initLoc, PtrState(ExplState.top()))), listOf()),
              EmptyProof.getInstance(),
            )
          }
        }
      }
    }
    SafetyResult.unknown()
  }
    as SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>
}

/**
 * Finds and merges all the different paths inbetween the two locations. For non-fully unrolled
 * lassos (i.e., there is a smaller loop inside the lasso), this will result in an infinite loop.
 */
private fun getNondetPath(current: XcfaLocation, final: XcfaLocation): Stmt {
  val outEdgeStmts =
    current.outgoingEdges.map {
      if (it.target == final) SequenceStmt.of(it.getFlatLabels().map(XcfaLabel::toStmt))
      else getNondetPath(it.target, final)
    }
  return if (outEdgeStmts.size == 1) outEdgeStmts.first()
  else if (outEdgeStmts.size > 1) NonDetStmt.of(outEdgeStmts)
  else error("Discontinuity in path @$current")
}

private data class LassoExprs(
  val stemExpr: Expr<BoolType>,
  val recCond: Expr<BoolType>,
  val transRel: Expr<BoolType>,
)
