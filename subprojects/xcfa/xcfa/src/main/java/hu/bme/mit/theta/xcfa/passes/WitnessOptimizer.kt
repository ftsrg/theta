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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.intersect
import hu.bme.mit.theta.xcfa.utils.simplify
import java.math.BigInteger

/**
 * Optimizes witness-specific XCFA instrumentation after witness parsing.
 *
 * The pass propagates literal input parameters through the procedure, keeps only values that agree
 * on all incoming edges at joins, and simplifies edge labels with the resulting valuation. It also
 * normalizes witness segment-counter updates by turning guarded counter assignments into explicit
 * assumptions followed by concrete assignments, removing duplicate segment updates and trivial
 * labels. Thread-start parameters guarded by the segment counter are rewritten similarly, by
 * extracting the guard as an assumption and passing the selected literal value to the start label.
 */
class WitnessOptimizer(private val params: List<Expr<*>>, private val parseContext: ParseContext) :
  ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    // This pass exists to normalize the segment counters ApplyWitnessPass inserts when *validating*
    // an input witness; without a witness there are none, and its only other effect -- propagating
    // the thread-start literal arguments through the body -- is redundant, since the OC event graph
    // already binds each start parameter (XcfaToEventGraph). So with no segment counter there is
    // nothing to do, and running the forward propagation anyway deadlocks on any loop in the thread
    // body (it waits for every incoming edge of a location, which a loop head never gets).
    val hasSegmentCounter =
      builder.getEdges().any { edge ->
        edge.label.getFlatLabels().any { label ->
          label.collectVars().any { it.name == SEGMENT_COUNTER }
        }
      }
    if (!hasSegmentCounter) {
      return builder
    }

    val initialValuation = MutableValuation()
    builder.getParams().forEachIndexed { index, param ->
      if (param.second == ParamDirection.IN && index < params.size && params[index] is LitExpr<*>) {
        initialValuation.put(param.first, params[index] as LitExpr<*>)
      }
    }

    val waitlist =
      mutableMapOf(builder.initLoc to mutableListOf(initialValuation to setOf<BigInteger>()))
    while (waitlist.isNotEmpty()) {
      val (loc, valuations) =
        waitlist.firstNotNullOf { (loc, valuations) ->
          if (valuations.size >= loc.incomingEdges.size) loc to valuations else null
        }
      waitlist.remove(loc)
      val mergedValuation = MutableValuation.copyOf(valuations.map { it.first }.reduce(::intersect))

      loc.outgoingEdges.toList().forEach { edge ->
        val oldLabels = edge.getFlatLabels()
        val simplifiedLabels =
          oldLabels.flatMap {
            val simplified = it.simplify(mergedValuation, parseContext)
            simplifyStartLabelLogicalThread(simplified) ?: listOf(simplified)
          }
        builder.parent.getVars().forEach { mergedValuation.remove(it.wrappedVar) }

        val loopSegmentUpdates = valuations.flatMap { it.second }.toMutableSet()
        val newLabels =
          simplifySegmentCounterAssignments(simplifiedLabels, loopSegmentUpdates).filter {
            if (it is StmtLabel) {
              if (it.stmt is AssignStmt<*> && it.stmt.varDecl.name == SEGMENT_COUNTER) {
                val expr = it.stmt.expr
                if (expr is RefExpr<*> && expr.decl.name == SEGMENT_COUNTER) {
                  return@filter false
                }
              } else if (it.stmt is AssumeStmt && it.stmt.cond == True()) {
                return@filter false
              }
            }
            true
          }

        if (newLabels != oldLabels) {
          builder.removeEdge(edge)
          builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
        }
        waitlist
          .getOrPut(edge.target) { mutableListOf() }
          .add(mergedValuation to loopSegmentUpdates)
      }
    }

    return builder
  }

  private fun simplifySegmentCounterAssignments(
    labels: List<XcfaLabel>,
    alreadyUsedSegmentUpdates: MutableSet<BigInteger>,
  ): List<XcfaLabel> {
    var updatedSegment = false
    val newLabels = mutableListOf<XcfaLabel>()
    labels.forEach {
      val segmentUpdate = getCurrentSegmentFromSegmentCounterUpdate(it)
      if (segmentUpdate != null) {
        val value = segmentUpdate.then.value
        if (updatedSegment || value in alreadyUsedSegmentUpdates) {
          // do not add the segment update
        } else {
          alreadyUsedSegmentUpdates.add(value)
          updatedSegment = true
          var insertIndex = newLabels.size
          while (insertIndex > 0) {
            val l = newLabels[insertIndex - 1]
            if (l is StmtLabel && l.stmt is AssumeStmt) {
              insertIndex--
            } else {
              break
            }
          }
          newLabels.add(insertIndex, StmtLabel(AssumeStmt.of(segmentUpdate.cond)))
          newLabels.add(
            AssignStmtLabel(segmentUpdate.varDecl, segmentUpdate.then, segmentUpdate.metadata)
          )
        }
      } else {
        newLabels.add(it)
      }
    }

    val valuation = MutableValuation()
    return newLabels.map {
      val result = it.simplify(valuation, parseContext)
      if (result is StmtLabel) {
        val stmt = result.stmt
        if (stmt is AssumeStmt) {
          val cond = stmt.cond
          if (cond is EqExpr<*>) {
            val left = cond.leftOp
            val right = cond.rightOp
            if (left is RefExpr<*> && left.decl.name == SEGMENT_COUNTER && right is LitExpr<*>) {
              valuation.put(left.decl, right)
            } else if (
              right is RefExpr<*> && right.decl.name == SEGMENT_COUNTER && left is LitExpr<*>
            ) {
              valuation.put(right.decl, left)
            }
          }
        }
      }
      result
    }
  }

  private data class SegmentUpdate(
    val varDecl: VarDecl<*>,
    val cond: EqExpr<*>,
    val then: IntLitExpr,
    val metadata: MetaData,
  )

  private fun getCurrentSegmentFromSegmentCounterUpdate(label: XcfaLabel): SegmentUpdate? {
    if (label is StmtLabel) {
      val stmt = label.stmt
      if (stmt is AssignStmt<*>) {
        if (stmt.varDecl.name == SEGMENT_COUNTER) {
          val expr = stmt.expr
          if (expr is IteExpr<*>) {
            val cond = expr.cond
            val then = expr.then
            if (cond is EqExpr<*> && then is IntLitExpr) {
              return SegmentUpdate(stmt.varDecl, cond, then, label.metadata)
            }
          }
        }
      }
    }
    return null
  }

  private fun simplifyStartLabelLogicalThread(label: XcfaLabel): List<XcfaLabel>? {
    if (label !is StartLabel) return null
    var assumption: AssumeStmt? = null
    val newParams =
      label.params.map {
        if (it is IteExpr) {
          val cond = it.cond
          val then = it.then
          if (cond is EqExpr<*> && then is LitExpr<*>) {
            val left = cond.leftOp
            if (left is RefExpr<*> && left.decl.name == SEGMENT_COUNTER) {
              assumption = AssumeStmt.of(cond)
              return@map then
            }
          }
        }
        it
      }
    if (assumption == null) return null
    return listOf(StmtLabel(assumption), label.copy(params = newParams))
  }
}
