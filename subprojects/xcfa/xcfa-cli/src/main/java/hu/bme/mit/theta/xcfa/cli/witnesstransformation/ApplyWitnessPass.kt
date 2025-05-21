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
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.statements.CDoWhile
import hu.bme.mit.theta.frontend.transformation.model.statements.CFor
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.frontend.transformation.model.statements.CWhile
import hu.bme.mit.theta.xcfa.AssignStmtLabel
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.witnesses.*
import java.util.LinkedList

class ApplyWitnessPass(val parseContext: ParseContext, val witness: YamlWitness) : ProcedurePass {
  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val segments = witness.content.map { c -> c.segment }.filterNotNull().iterator()

    val statementToEdge = LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>()
    for (edge in builder.getEdges()) {
      for (flatLabel in edge.label.getFlatLabels()) {
        (flatLabel.metadata as? CMetaData)?.also {
          for (astNode in it.astNodes) {
            statementToEdge.add(Triple(astNode, flatLabel, edge))
            // for termination, we also need iteration statements' bodies
            if (astNode is CWhile) {
              statementToEdge.add(Triple(astNode.body, flatLabel, edge))
            } else if (astNode is CFor) {
              statementToEdge.add(Triple(astNode.body, flatLabel, edge))
            } else if (astNode is CDoWhile) {
              statementToEdge.add(Triple(astNode.body, flatLabel, edge))
            }
          }
        }
      }
    }

    val segmentCounter = Var("__THETA__segment__counter__", Int())
    builder.addVar(segmentCounter)

    for (outgoingEdge in builder.initLoc.outgoingEdges) {
      builder.removeEdge(outgoingEdge)
      builder.addEdge(
        outgoingEdge.withLabel(
          SequenceLabel(
            listOf(AssignStmtLabel(segmentCounter, Int(0))) + outgoingEdge.getFlatLabels()
          )
        )
      )
    }

    var i = 0
    var firstCycle = -1
    while (segments.hasNext()) {
      val nextSegment = segments.next()
      val wp = nextSegment.first { waypoint -> waypoint.waypoint.action != Action.AVOID }
      val loc = wp.waypoint.location
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
            WaypointType.BRANCHING -> {
              // no-op now
              True()
            }
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
        if (!segments.hasNext() && firstCycle != 1) {
          AssignStmtLabel(segmentCounter, Int(firstCycle))
        } else {
          AssignStmtLabel(
            segmentCounter,
            Ite<IntType>(currentSegmentPred, Add(segmentCounter.ref, Int(1)), segmentCounter.ref),
          )
        }

      val labelsOnEdges =
        statementToEdge
          .filter { (statement, _, _) ->
            statement.lineNumberStart == loc.line && statement.colNumberStart + 1 == loc.column
          }
          .map { (_, label, edge) -> Pair(label, edge) }

      for ((label, edge) in labelsOnEdges) {
        builder.removeEdge(edge)
        val newLabels = LinkedList(edge.getFlatLabels())
        val index = newLabels.indexOf(label)
        newLabels.add(index, StmtLabel(AssumeStmt.of(expr), ChoiceType.NONE, EmptyMetaData))
        newLabels.add(index + 1, segmentUpdate)
        builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
      }
    }

    builder.prop = Eq(segmentCounter.ref, Int(i))
    return builder
  }
}
