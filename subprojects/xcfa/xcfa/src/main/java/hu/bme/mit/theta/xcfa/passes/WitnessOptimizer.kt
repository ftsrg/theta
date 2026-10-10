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
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
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
    val segmentVar: VarDecl<*>? =
      builder.getEdges().firstNotNullOfOrNull { edge ->
        edge.label.getFlatLabels().firstNotNullOfOrNull { label ->
          label.collectVars().find { it.name == SEGMENT_COUNTER }
        }
      }
    if (segmentVar == null) {
      // This pass normalizes the segment counters ApplyWitnessPass inserts when *validating*
      // an input witness; without a witness there are none, so we can return
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
        val passedSegments = valuations.flatMap { it.second }.toMutableSet()
        val oldLabels = edge.getFlatLabels()
        val simplifiedLabels =
          oldLabels.flatMap {
            val simplified = it.simplify(mergedValuation, parseContext)
            simplifyStartLabelLogicalThread(simplified, passedSegments) ?: listOf(simplified)
          }
        builder.parent.getVars().forEach { mergedValuation.remove(it.wrappedVar) }

        val newLabels =
          simplifySegmentCounterUpdates(segmentVar, simplifiedLabels, passedSegments).filter {
            if (it is StmtLabel) {
              if (it.stmt is AssignStmt<*> && it.stmt.varDecl.name == SEGMENT_COUNTER) {
                val expr = it.stmt.expr
                if (expr is RefExpr<*> && expr.decl.name == SEGMENT_COUNTER) {
                  return@filter false
                } else if (expr is IntLitExpr) {
                  var i = BigInteger.valueOf(0)
                  while (i < expr.value) passedSegments.add(i++)
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
          .add(mergedValuation to passedSegments)
      }
    }

    return builder
  }

  private fun simplifySegmentCounterUpdates(
    segmentVar: VarDecl<*>,
    labels: List<XcfaLabel>,
    passedSegmentValues: MutableSet<BigInteger>,
  ): List<XcfaLabel> {
    var updatedSegment = false
    val newLabels = mutableListOf<XcfaLabel>()
    labels.forEach { label ->
      val segmentUpdates = getSegmentUpdates(label)
      if (segmentUpdates.isNotEmpty()) {
        val segmentUpdate = segmentUpdates.find { it.current.value !in passedSegmentValues }
        if (updatedSegment || segmentUpdate == null) {
          // do not add the segment update
        } else {
          passedSegmentValues.add(segmentUpdate.current.value)
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
            AssignStmtLabel(segmentVar, segmentUpdate.next, segmentUpdate.metadata)
          )
        }
      } else {
        newLabels.add(label)
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

  private data class SegmentAlternatives(
    val cond: Expr<BoolType>,
    val current: IntLitExpr,
    val next: IntLitExpr,
    val metadata: MetaData,
  )

  private fun getSegmentUpdates(label: XcfaLabel): List<SegmentAlternatives> =
    ((label as? StmtLabel)?.stmt as? AssignStmt<*>)
      ?.takeIf { stmt -> stmt.varDecl.name == SEGMENT_COUNTER }
      ?.let { stmt ->
        val updates = mutableSetOf<SegmentAlternatives>()
        var expr = stmt.expr
        while (expr is IteExpr<*>) {
          segmentIteValues<IntLitExpr>(expr)?.let { (current, next) ->
            updates.add(SegmentAlternatives(expr.cond, current, next, label.metadata))
          }
          expr = expr.`else`
        }
        updates.sortedBy { it.current }
      }
      ?: emptyList()

  private fun simplifyStartLabelLogicalThread(
    label: XcfaLabel,
    passedSegmentValues: Set<BigInteger>,
  ): List<XcfaLabel>? {
    if (label !is StartLabel) return null
    var assumption: AssumeStmt? = null
    val newParams =
      label.params.map { param ->
        var segmentCond: Expr<BoolType>? = null
        var nextSegmentAlternative: LitExpr<*>? = null
        var minNotPassedSegment: BigInteger? = null
        var expr = param
        while (expr is IteExpr<*>) {
          segmentIteValues<LitExpr<*>>(expr)?.let { (segmentValue, paramValue) ->
            if (segmentValue.value !in passedSegmentValues) {
              if (minNotPassedSegment == null || segmentValue.value < minNotPassedSegment) {
                segmentCond = expr.cond
                nextSegmentAlternative = paramValue
                minNotPassedSegment = segmentValue.value
              }
            }
          }
          expr = expr.`else`
        }

        if (nextSegmentAlternative != null) {
          assumption = Assume(segmentCond)
          nextSegmentAlternative
        } else param
      }
    return if (assumption == null) null
      else listOf(StmtLabel(assumption), label.copy(params = newParams))
  }

  private inline fun <reified L : Expr<*>> segmentIteValues(e: IteExpr<*>): Pair<IntLitExpr, L>? {
    val eq = e.cond as? EqExpr<*> ?: return null
    if ((eq.leftOp as? RefExpr<*>)?.decl?.name != SEGMENT_COUNTER) return null
    val current = eq.rightOp as? IntLitExpr ?: return null
    val next = e.then as? L ?: return null
    return current to next
  }
}
