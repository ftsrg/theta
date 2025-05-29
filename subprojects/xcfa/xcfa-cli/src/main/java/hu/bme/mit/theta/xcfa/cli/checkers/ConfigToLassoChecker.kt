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
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.cli.params.LassoCheckerConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getSolver
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.getStatementToEdge
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.witnesses.Action
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import java.util.LinkedList
import kotlinx.serialization.builtins.ListSerializer

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

  val stmtToEdge = getStatementToEdge(proc)

  val witness =
    WitnessYamlConfig.decodeFromString(
        ListSerializer(YamlWitness.serializer()),
        config.inputConfig.witness?.readText() ?: error("No witness in config!"),
      )[0]

  val stem = LinkedList<Stmt>()
  val cycle = LinkedList<Stmt>()

  var lastSet: Set<Pair<XcfaLabel?, XcfaEdge>> =
    proc.initLoc.outgoingEdges.map { Pair(it.getFlatLabels()[0], it) }.toSet()
  var lastAction = Action.FOLLOW

  val firstCycle =
    witness.content.indexOfFirst { it.segment!!.any { it.waypoint.action == Action.CYCLE } }

  val content = witness.content + witness.content[firstCycle]

  for (item in content) {
    val wp = item.segment?.first { it.waypoint.action != Action.AVOID }?.waypoint!!

    val relevantStmts =
      stmtToEdge
        .filter {
          it.first.lineNumberStart == wp.location.line &&
            it.first.colNumberStart + 1 == wp.location.column
        }
        .let { stmts ->
          if (stmts.map { it.third }.toSet().size == 1) {
            val label =
              stmts.first().third.getFlatLabels().first { stmts.map { it.second }.contains(it) }
            stmts.filter { it.second == label }
          } else {
            stmts
          }
        }
        .map { Pair(it.second, it.third) }

    val tuples = lastSet * relevantStmts
    val stmt =
      if (tuples.size == 1) {
        val (from, to) = tuples[0]
        getNondetPath(from.first, from.second, to.first, to.second)
      } else {
        NonDetStmt.of(
          tuples.map { (from, to) -> getNondetPath(from.first, from.second, to.first, to.second) }
        )
      }

    if (lastAction == Action.FOLLOW) {
      stem.add(stmt)
    } else {
      cycle.add(stmt)
    }

    lastSet = relevantStmts.toSet()
    lastAction = wp.action
  }

  return SafetyChecker<
    EmptyProof,
    Trace<XcfaState<PtrState<ExplState>>, XcfaAction>,
    XcfaPrec<PtrPrec<ExplPrec>>,
  > {
    val solver = solverFactory.createSolver()

    val stemExpr =
      PathUtils.unfold(And(StmtUtils.toExpr(SequenceStmt.of(stem), indexing(0)).exprs), indexing(0))

    val cycleUnfoldResult = StmtUtils.toExpr(SequenceStmt.of(cycle), indexing(0))
    val unfoldedCycle = PathUtils.unfold(And(cycleUnfoldResult.exprs), indexing(0))

    var vars = xcfa.collectVars()

    val segmentCounter = vars.first { it.name == "__THETA__segment__counter__" }
    val segmentPassed = vars.first { it.name == "__THETA__last__segment__passed__" }

    vars = vars - setOf(segmentPassed, segmentCounter)

    val cycleExpr =
      And(
        vars.map {
          Eq(it.getConstDecl(0).ref, it.getConstDecl(cycleUnfoldResult.indexing.get(it)).ref)
        } + Eq(segmentCounter.getConstDecl(0).ref, Int(firstCycle)) + unfoldedCycle
      )

    WithPushPop(solver).use {
      logger.writeln(Logger.Level.INFO, "Checking recurrence location reachability..")
      solver.add(stemExpr)
      //      val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())
      //      solver.assertions.forEach { logger.writeln(Logger.Level.INFO, manager.toTerm(it)) }
      solver.check()
      if (solver.status.isUnsat) {
        logger.writeln(Logger.Level.INFO, "Recurrence location reachability failed.")
        return@SafetyChecker SafetyResult.unknown()
      } else {
        logger.writeln(Logger.Level.INFO, "Recurrence location reachability successful.")
      }
    }

    WithPushPop(solver).use {
      logger.writeln(Logger.Level.INFO, "Checking recurrence location re-reachability..")
      solver.add(cycleExpr)
      //      val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())
      //      solver.assertions.forEach { logger.writeln(Logger.Level.INFO, manager.toTerm(it)) }
      solver.check()
      if (solver.status.isUnsat) {
        logger.writeln(Logger.Level.INFO, "Recurrence location re-reachability failed.")
      } else {
        val model = solver.model.toMap()
        logger.writeln(
          Logger.Level.INFO,
          "Recurrence location re-reachability successful. A recurrence set: ${vars
            .filter { parseContext.metadata.getMetadataValue(it.name, "cName").isPresent }
            .associateWith {model[it.getConstDecl(0)]}
            .map { "${parseContext.metadata.getMetadataValue(it.key.name, "cName").get()} == ${it.value}" }
            .joinToString(" && ")
          } at ${witness.content[firstCycle].segment!!.first{ it.waypoint.action == Action.CYCLE }.waypoint.location}",
        )
        return@SafetyChecker SafetyResult.unsafe(
          Trace.of(listOf(XcfaState(xcfa, proc.initLoc, PtrState(ExplState.top()))), listOf()),
          EmptyProof.getInstance(),
        )
      }
    }

    SafetyResult.unknown()
  }
    as SafetyChecker<EmptyProof, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>
}

private fun getNondetPath(
  label1: XcfaLabel?,
  edge1: XcfaEdge,
  label2: XcfaLabel,
  edge2: XcfaEdge,
): Stmt {
  val edge1labels = edge1.getFlatLabels()
  val edge2labels = edge2.getFlatLabels()
  val idx1 = if (label1 == null) 0 else edge1labels.indexOf(label1)
  val idx2 = edge2labels.indexOf(label2)

  if (edge1 == edge2 && idx1 < idx2) {
    return SequenceStmt.of(edge1labels.subList(idx1, idx2).map { it.toStmt() })
  }

  // adding initial labels
  val labels = LinkedList(edge1labels.subList(idx1, edge1labels.size).map { it.toStmt() })

  // adding paths in-between
  labels.add(getNondetPath(edge1.target, edge2.source))

  // adding final labels, up to (but not including) label2
  labels.addAll(edge2labels.subList(0, idx2).map { it.toStmt() })
  return SequenceStmt.of(labels)
}

private fun getNondetPath(current: XcfaLocation, final: XcfaLocation): Stmt {
  val outEdgeStmts =
    current.outgoingEdges.map {
      if (it.target == final) SequenceStmt.of(it.getFlatLabels().map(XcfaLabel::toStmt))
      else getNondetPath(it.target, final)
    }
  return if (outEdgeStmts.size == 1) outEdgeStmts.first()
  else if (outEdgeStmts.size > 1) NonDetStmt.of(outEdgeStmts) else SkipStmt.getInstance()
}

operator fun <T1, T2> Iterable<T1>.times(other: Iterable<T2>) =
  this.flatMap { a -> other.map { b -> a to b } }
