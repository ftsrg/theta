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
package hu.bme.mit.theta.xcfa.cli.witnesstransformation

import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.c2xcfa.getExpressionFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs.Ite
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.statements.CDoWhile
import hu.bme.mit.theta.frontend.transformation.model.statements.CFor
import hu.bme.mit.theta.frontend.transformation.model.statements.CIf
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.frontend.transformation.model.statements.CWhile
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.*
import java.util.LinkedList

class ApplyWitnessPass(val parseContext: ParseContext, val witness: YamlWitness) : ProcedurePass {
  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (builder.parent.getInitProcedures().none { it.first.equals(builder) }) {
      return builder
    }
    val segments = witness.content.map { c -> c.segment }.filterNotNull().iterator()
    val segmentCount = witness.content.map { c -> c.segment }.filterNotNull().count()

    val segmentCounter = Var("__THETA__segment__counter__", Int())
    builder.addVar(segmentCounter)

    val segmentFlag = Var("__THETA__last__segment__passed__", Bool())
    builder.addVar(segmentFlag)

    for (outgoingEdge in builder.initLoc.outgoingEdges) {
      builder.removeEdge(outgoingEdge)
      builder.addEdge(
        outgoingEdge.withLabel(
          SequenceLabel(
            listOf(AssignStmtLabel(segmentCounter, Int(0)), AssignStmtLabel(segmentFlag, False())) +
              outgoingEdge.getFlatLabels()
          )
        )
      )
    }

    val modifications = LinkedHashMap<XcfaEdge, MutableList<Annotation>>()

    var i = 0
    var firstCycle = -1
    val statementToEdge = getStatementToEdge(builder)
    while (segments.hasNext()) {

      val nextSegment = segments.next()
      val wp = nextSegment.first { waypoint -> waypoint.waypoint.action != Action.AVOID }
      var loc = wp.waypoint.location
      val currentSegmentPred = Eq(segmentCounter.ref, Int(i))
      if (wp.waypoint.action == Action.CYCLE && firstCycle == -1) {
        firstCycle = i
      }
      i++
      val expr =
        Imply(
          currentSegmentPred,
          when (wp.waypoint.type) {
            WaypointType.ASSUMPTION -> {
              val constraint = wp.waypoint.constraint!!
              check(constraint.format!! == Format.C_EXPRESSION) { "Not handled: $constraint" }
              getExpressionFromC(
                constraint.value,
                parseContext,
                false,
                false,
                NullLogger.getInstance(),
                builder.getVars() + builder.parent.getVars().map { it.wrappedVar },
              )
            }
            WaypointType
              .FUNCTION_RETURN -> { // TODO: deduplicate with below code for statement search
              val vars =
                statementToEdge
                  .filter { (statement, label, _) ->
                    statement.lineNumberStart == loc.line &&
                      (statement.colNumberStop + 1 - 1 == loc.column ||
                        statement.colNumberStop + 1 == loc.column) &&
                      label is StmtLabel &&
                      label.stmt is HavocStmt<*>
                  }
                  .map { (_, label, _) -> ((label as StmtLabel).stmt as HavocStmt<*>).varDecl }

              if (vars.size != 1) {
                True() // no or multiple vars
              } else {
                val v = vars.first()
                val cNameOpt = parseContext.metadata.getMetadataValue(v.name, "cName")
                if (cNameOpt.isPresent) {
                  val constraint = wp.waypoint.constraint!!
                  check(constraint.format!! == Format.C_EXPRESSION) { "Not handled: $constraint" }
                  getExpressionFromC(
                    constraint.value.replace("\\result", cNameOpt.get() as String),
                    parseContext,
                    false,
                    false,
                    NullLogger.getInstance(),
                    builder.getVars() + builder.parent.getVars().map { it.wrappedVar },
                  )
                } else {
                  True() // no cname
                }
              }
            }
            WaypointType.BRANCHING -> {
              val branching =
                statementToEdge
                  .mapNotNull { (statement, _, _) ->
                    if (
                      statement.lineNumberStart == loc.line &&
                        statement.colNumberStart + 1 == loc.column
                    )
                      statement
                    else null
                  }
                  .map {
                    when (it) {
                      is CWhile,
                      is CFor,
                      is CIf,
                      is CDoWhile -> it
                      else -> error("Branching not on iteration/branching statement.")
                    }
                  }
                  .first() // we hope it's a single ast node..

              val guardAssume =
                statementToEdge.mapNotNull {
                  if (
                    it.first == branching &&
                      it.second is StmtLabel &&
                      (it.second as StmtLabel).stmt is AssumeStmt &&
                      (it.second as StmtLabel).choiceType != ChoiceType.NONE
                  )
                    Pair(
                      (it.second as StmtLabel).choiceType,
                      (it.second as StmtLabel).stmt as AssumeStmt,
                    )
                  else null
                }

              when (wp.waypoint.constraint?.value) {
                "true" -> {
                  guardAssume.first { it.first == ChoiceType.MAIN_PATH }.second.cond
                }
                "false" -> {
                  guardAssume.first { it.first == ChoiceType.ALTERNATIVE_PATH }.second.cond
                }
                else -> {
                  error("Unknown value for branching: ${wp.waypoint.constraint?.value}")
                }
              }
            }
            WaypointType.FUNCTION_ENTER,
            WaypointType.TARGET -> {
              // no-op now
              True()
            }
            else -> {
              error("Not handled: ${wp.waypoint.type}")
            }
          },
        )

      val segmentUpdate =
        if (!segments.hasNext() && firstCycle > -1) {
          Pair(currentSegmentPred, Int(firstCycle))
        } else if (segments.hasNext()) {
          Pair(currentSegmentPred, Int(i)) // here i was already incremented
        } else {
          null
        }

      val segmentFlagUpdate =
        if (i == segmentCount) {
          AssignStmtLabel(segmentFlag, Ite(currentSegmentPred, currentSegmentPred, segmentFlag.ref))
        } else null

      val labelsOnEdges =
        statementToEdge
          .filter { (statement, label, _) ->
            if (wp.waypoint.type == WaypointType.FUNCTION_RETURN) {
              statement.lineNumberStart == loc.line &&
                (statement.colNumberStop + 1 - 1 == loc.column ||
                  statement.colNumberStop + 1 == loc.column) &&
                label is StmtLabel &&
                label.stmt is HavocStmt<*>
            } else {
              statement.lineNumberStart == loc.line && statement.colNumberStart + 1 == loc.column
            }
          }
          .map { (_, label, edge) -> Pair(label, edge) }

      val edgeLabels = LinkedHashMap<XcfaEdge, MutableList<XcfaLabel>>()
      for ((label, edge) in labelsOnEdges) {
        edgeLabels.computeIfAbsent(edge) { LinkedList() }.add(label)
      }

      for ((edge, labels) in edgeLabels) {
        val oldLabels = edge.getFlatLabels()
        val labels =
          labels
            .map { label ->
              oldLabels.indexOf(label) +
                if (wp.waypoint.type == WaypointType.FUNCTION_RETURN) 1
                else 0 // for function_return, we want to add it next.
            }
            .sorted()
            .map { oldLabels[it] }
        for (label in labels) {
          modifications
            .computeIfAbsent(edge) { LinkedList() }
            .add(
              Annotation(
                edge,
                label,
                StmtLabel(AssumeStmt.of(expr), ChoiceType.NONE, EmptyMetaData),
                segmentUpdate,
                segmentFlagUpdate,
              )
            )
        }
      }
    }

    modifications.forEach { (edge, allAnnots) ->
      builder.removeEdge(edge)
      val oldLabels = edge.getFlatLabels()
      val newLabels = LinkedList<XcfaLabel>()
      val indexToAnnots =
        allAnnots.groupBy { oldLabels.indexOf(it.beforeLabel) }.toList().sortedBy { it.first }
      var i = 0
      for ((index, annots) in indexToAnnots) {
        while (i < index) {
          newLabels.add(oldLabels[i++])
        }
        newLabels.addAll(annots.map { it.assumption })
        newLabels.addAll(annots.mapNotNull { it.flagUpdate })
        var expr = segmentCounter.ref as Expr<IntType>
        for ((cond, then) in annots.mapNotNull { it.segmentUpdate }) {
          expr = Ite(cond, then, expr)
        }
        newLabels.add(AssignStmtLabel(segmentCounter, expr))
      }
      while (i < oldLabels.size) {
        newLabels.add(oldLabels[i++])
      }
      builder.addEdge(edge.withLabel(SequenceLabel(newLabels, edge.label.metadata)))
    }

    builder.prop = segmentFlag.ref
    return builder
  }
}

fun getStatementToEdge(
  builder: XcfaProcedureBuilder
): LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>> {
  val statementToEdge = LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>()
  for (edge in builder.getEdges()) {
    extractEdge(edge, statementToEdge)
  }
  return statementToEdge
}

fun getStatementToEdge(
  proc: XcfaProcedure
): LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>> {
  val statementToEdge = LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>()
  for (edge in proc.edges) {
    extractEdge(edge, statementToEdge)
  }
  return statementToEdge
}

private fun extractEdge(
  edge: XcfaEdge,
  statementToEdge: LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>,
) {
  for (flatLabel in edge.label.getFlatLabels()) {
    (flatLabel.metadata as? CMetaData)?.also {
      for (astNode in it.astNodes) {
        statementToEdge.add(Triple(astNode, flatLabel, edge))
        // for termination, we also need iteration statements' bodies
        //        if (astNode is CWhile) {
        //          statementToEdge.add(Triple(astNode.body, flatLabel, edge))
        //        } else if (astNode is CFor) {
        //          statementToEdge.add(Triple(astNode.body, flatLabel, edge))
        //        } else if (astNode is CDoWhile) {
        //          statementToEdge.add(Triple(astNode.body, flatLabel, edge))
        //        }
      }
    }
  }
}

private data class Annotation(
  val edge: XcfaEdge,
  val beforeLabel: XcfaLabel,
  val assumption: XcfaLabel,
  val segmentUpdate: Pair<Expr<BoolType>, Expr<IntType>>?,
  val flagUpdate: XcfaLabel?,
) {}
