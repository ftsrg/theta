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
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.getCMetaData
import hu.bme.mit.theta.c2xcfa.getExpressionFromC
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.LassoValidationConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.ApplyWitnessPassesManager
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.witnesses.*
import kotlinx.serialization.builtins.ListSerializer

fun getLassoValidationChecker(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
  warningLogger: Logger,
): SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {

  val witnessConfig = config.backendConfig.specConfig as LassoValidationConfig

  val witness =
    WitnessYamlConfig.decodeFromString(
        ListSerializer(YamlWitness.serializer()),
        witnessConfig.witness!!.readText(),
      )
      .get(0)

  val recurrenceSets =
    witness.content.filter {
      it.segment?.get(0)?.waypoint?.type == WaypointType.RECURRENCE_CONDITION
    }
  check(recurrenceSets.size == 1) { "Single recurrence set not found." }
  val recurrenceSet = recurrenceSets.first()
  val constraint = recurrenceSet.segment!![0].waypoint.constraint!!
  val recurrenceSetExpr =
    if (constraint.format == Format.C_EXPRESSION) {
      getExpressionFromC(
        constraint.value,
        parseContext,
        false,
        false,
        warningLogger,
        xcfa.collectVars(),
      )
    } else TODO("Not handled: ${constraint.format}")

  val stemRecurrentLocCount = 0

  val recurrenceWaypoint = recurrenceSet.segment!![0]
  val recurrenceSetLocation = recurrenceWaypoint.waypoint.location
  val waypoints = witness.content.flatMap { it.segment ?: emptyList() }

  check(
    waypoints.find { w ->
      w.waypoint.location == recurrenceSetLocation && w.waypoint.action != Action.CYCLE
    } == null
  ) {
    "Theta does not yet support visiting the recurrence location in the stem"
  }

  val lasso =
    xcfa.optimizeFurther(ApplyWitnessPassesManager(parseContext, witness)).initProcedures[0].first

  return SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>> {
    val honda = findRecurrenceLocation(lasso, recurrenceWaypoint)

    val stem = getNondetPath(lasso.initLoc, honda)
    val cycle = getNondetPath(honda, honda)

    val stemExpr =
      PathUtils.unfold(
        And(
          StmtUtils.toExpr(
              SequenceStmt.of(listOf(stem, Assume(recurrenceSetExpr))),
              VarIndexingFactory.basicVarIndexing(0),
            )
            .exprs
        ),
        VarIndexingFactory.basicVarIndexing(0),
      )
    val cycleExpr =
      PathUtils.unfold(
        And(
          StmtUtils.toExpr(
              listOf(cycle, Assume(recurrenceSetExpr)),
              VarIndexingFactory.basicVarIndexing(0),
            )
            .exprs
        ),
        VarIndexingFactory.basicVarIndexing(0),
      )

    val solver = getSolver(witnessConfig.solver, witnessConfig.validateSolver).createSolver()

    WithPushPop(solver).use {
      logger.writeln(Logger.Level.INFO, "Checking recurrence location reachability..")
      solver.add(stemExpr)
      solver.check()
      if (solver.status.isUnsat) {
        logger.writeln(
          Logger.Level.INFO,
          "Recurrence location reachability failed. Current assertions:",
        )
        val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())
        solver.assertions.forEach { logger.writeln(Logger.Level.INFO, manager.toTerm(it)) }
        return@SafetyChecker SafetyResult.safe(EmptyProof.getInstance())
      }
      logger.writeln(Logger.Level.INFO, "Recurrence location reachability successful.")
    }

    WithPushPop(solver).use {
      logger.writeln(Logger.Level.INFO, "Checking recurrence set re-reachability..")
      val consts =
        ExprUtils.getIndexedConstants(cycleExpr)
          .filter { it.index == 0 }
          .associateWith { Param(it.varDecl.name, it.varDecl.type) }
      val vars = consts.map { Pair(it.key.varDecl, it.value) }.toMap()
      val forall =
        ExprUtils.simplify(
          Forall(
            consts.values,
            Imply(
              ExprUtils.changeDecls(recurrenceSetExpr, vars),
              ExprUtils.changeDecls(cycleExpr, consts),
            ),
          )
        )
      solver.add(forall)
      solver.check()
      if (solver.status.isUnsat) {
        logger.writeln(
          Logger.Level.INFO,
          "Recurrence set re-reachability failed. Current assertions:",
        )
        val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())
        solver.assertions.forEach { logger.writeln(Logger.Level.INFO, manager.toTerm(it)) }
        return@SafetyChecker SafetyResult.safe(EmptyProof.getInstance())
      }
      logger.writeln(Logger.Level.INFO, "Recurrence set re-reachability successful.")
    }

    SafetyResult.unsafe(
      Trace.of(listOf(XcfaState(xcfa, lasso.initLoc, PtrState(ExplState.top()))), listOf()),
      EmptyProof.getInstance(),
    )
  }
}

private fun findRecurrenceLocation(lasso: XcfaProcedure, recurrenceSet: Waypoint): XcfaLocation {
  val results = mutableSetOf<XcfaLocation>()
  val resultStatements = mutableSetOf<CStatement>()
  for (loc in lasso.locs.filter { it -> it.incomingEdges.size >= 1 }) {
    for (outEdge in loc.outgoingEdges) {
      val astNodes = outEdge.getCMetaData()!!.astNodes
      for (node in astNodes) {
        if (
          node.lineNumberStart == recurrenceSet.waypoint.location.line &&
            node.colNumberStart + 1 == recurrenceSet.waypoint.location.column
        ) {
          results.add(loc)
          resultStatements.add(node)
        }
      }
    }
  }

  check(resultStatements.size == 1) {
    "Exactly one C statement should be possible to match to recurrence location"
  }
  check(results.size == 1) { "There should only be one recurrence location in XCFA" }

  return results.iterator().next()
}

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
