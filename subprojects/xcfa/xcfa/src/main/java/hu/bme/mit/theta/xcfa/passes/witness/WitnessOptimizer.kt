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

package hu.bme.mit.theta.xcfa.passes.witness

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
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.LOGICAL_THREAD_ID
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
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
 *
 * Only the update of this procedure's [next segment][Segments.next] may become an assumption, and
 * only if that is sound: either the path passed every lower segment, so the counter is certain
 * there, or a single label of the whole program can fire the segment, and only in this thread, so a
 * path passing it early cannot follow the witness. Any other guarded update may or may not fire
 * (e.g., a loop head visited before the segment is due), so it is kept as it is.
 */
class WitnessOptimizer(
  private val params: List<Expr<*>>,
  private val parseContext: ParseContext,
  private val procedureName: String? = null,
) : ProcedurePass {

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

    // the segments this procedure's own waypoints pass; the others are left to other threads
    val labels = builder.getEdges().flatMap { it.getFlatLabels() }
    val threadId = logicalThreadId(labels, initialValuation)
    val alternatives = labels.map { segmentValues(it, threadId).distinct() }
    val ownSegments = alternatives.flatten().map { it.first }.toSortedSet()
    val unique = uniqueSegments(builder, labels, alternatives)
    val segments = Segments(ownSegments, unique)

    // Other threads may write globals and memory between two edges, so only locals carry over.
    val localVars = builder.getVars() + builder.getParams().map { it.first }
    val waitlist =
      mutableMapOf(builder.initLoc to mutableListOf(initialValuation to setOf<BigInteger>()))
    while (waitlist.isNotEmpty()) {
      val (loc, valuations) =
        waitlist.firstNotNullOf { (loc, valuations) ->
          if (valuations.size >= loc.incomingEdges.size) loc to valuations else null
        }
      waitlist.remove(loc)
      val mergedValuation = valuations.map { it.first }.reduce(::intersect)

      loc.outgoingEdges.toList().forEach { edge ->
        // simplifying an edge updates the valuation, so each edge needs its own copy
        val edgeValuation = MutableValuation.copyOf(mergedValuation)
        // a segment is only passed at a join if it is passed on every incoming path
        val passedSegments =
          valuations.map { it.second }.reduce { a, b -> a intersect b }.toMutableSet()
        val oldLabels = edge.getFlatLabels()
        val simplifiedLabels =
          oldLabels.flatMap {
            val simplified = it.simplify(edgeValuation, parseContext)
            simplifyStartLabelLogicalThread(simplified, passedSegments, segments)
              ?: listOf(simplified)
          }
        edgeValuation.decls.filter { it !in localVars }.forEach { edgeValuation.remove(it) }

        val newLabels =
          simplifySegmentCounterUpdates(segmentVar, simplifiedLabels, passedSegments, segments)
            .filter {
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
        waitlist.getOrPut(edge.target) { mutableListOf() }.add(edgeValuation to passedSegments)
      }
    }

    return builder
  }

  /**
   * The segments of [alternatives] no label but one of this procedure can fire, and which only this
   * thread fires there: the procedure runs in a single thread, or the alternative is guarded by
   * this thread's id.
   */
  private fun uniqueSegments(
    builder: XcfaProcedureBuilder,
    labels: List<XcfaLabel>,
    alternatives: List<List<Pair<BigInteger, Boolean>>>,
  ): Set<BigInteger> {
    val procedures = runCatching { builder.parent.getProcedures() }.getOrNull() ?: return setOf()
    val others = procedures.filter { it !== builder }
    val fired =
      (labels + others.flatMap { p -> p.getEdges().flatMap { it.getFlatLabels() } }).map {
        firedSegments(it) ?: return setOf()
      }
    val firing = fired.flatten().groupingBy { it }.eachCount()
    val name = { p: XcfaProcedureBuilder -> if (p === builder) procedureName ?: p.name else p.name }
    val single = instances(name(builder), procedures, name, setOf()) <= 1
    return alternatives
      .flatten()
      .filter { (segment, guarded) -> firing[segment] == 1 && (single || guarded) }
      .map { it.first }
      .toSet()
  }

  /**
   * The segments [label] may fire, i.e., the guards of segment-counter ites anywhere in it (also
   * those a temporary carries to the counter); null for a label that cannot be inspected.
   */
  private fun firedSegments(label: XcfaLabel): Set<BigInteger>? {
    val stmt = (label as? StmtLabel)?.stmt
    val exprs =
      when {
        label is StartLabel -> label.params
        label is InvokeLabel -> label.params
        stmt is AssignStmt<*> -> listOf(stmt.expr)
        stmt is AssumeStmt -> listOf(stmt.cond)
        label.collectVars().none { it.name == SEGMENT_COUNTER } -> listOf()
        else -> return null
      }
    return exprs.flatMap(::iteSegments).toSet()
  }

  private fun iteSegments(expr: Expr<*>): List<BigInteger> =
    listOfNotNull((expr as? IteExpr<*>)?.let { ownSegment(it.cond, null)?.first }) +
      expr.ops.flatMap(::iteSegments)

  /** How many threads may run [procedure], capped at 2. */
  private fun instances(
    procedure: String,
    procedures: Collection<XcfaProcedureBuilder>,
    name: (XcfaProcedureBuilder) -> String,
    seen: Set<String>,
  ): Int {
    if (procedure in seen) return 2
    val callers =
      procedures.flatMap { p ->
        p.getEdges()
          .flatMap { it.getFlatLabels() }
          .filter {
            (it as? StartLabel)?.name == procedure || (it as? InvokeLabel)?.name == procedure
          }
          .map { name(p) }
      }
    if (callers.isEmpty()) return 1
    return callers.sumOf { instances(it, procedures, name, seen + procedure) }.coerceAtMost(2)
  }

  /** The literal this procedure's logical thread id is set to, if it is known before the run. */
  private fun logicalThreadId(labels: List<XcfaLabel>, initial: MutableValuation): BigInteger? =
    labels
      .mapNotNull { ((it as? StmtLabel)?.stmt as? AssignStmt<*>) }
      .filter { it.varDecl.name == LOGICAL_THREAD_ID }
      .map { (ExprUtils.simplify(it.expr, initial) as? IntLitExpr)?.value }
      .distinct()
      .singleOrNull()

  /**
   * The segments whose guarded alternatives in [label] may fire in this thread (all but those
   * guarded by another logical thread id), each with whether it is guarded by [threadId].
   */
  private fun segmentValues(
    label: XcfaLabel,
    threadId: BigInteger?,
  ): List<Pair<BigInteger, Boolean>> {
    val exprs =
      if (label is StartLabel) label.params
      else
        listOfNotNull(
          ((label as? StmtLabel)?.stmt as? AssignStmt<*>)
            ?.takeIf { it.varDecl.name == SEGMENT_COUNTER }
            ?.expr
        )
    return exprs.flatMap { expr ->
      generateSequence(expr as? IteExpr<*>) { it.`else` as? IteExpr<*> }
        .mapNotNull { ownSegment(it.cond, threadId) }
        .toList()
    }
  }

  private fun ownSegment(cond: Expr<BoolType>, threadId: BigInteger?): Pair<BigInteger, Boolean>? {
    val conjuncts = if (cond is AndExpr) cond.ops else listOf(cond)
    var segment: BigInteger? = null
    var guarded = false
    for (eq in conjuncts.filterIsInstance<EqExpr<*>>()) {
      val name = (eq.leftOp as? RefExpr<*>)?.decl?.name
      val value = (eq.rightOp as? IntLitExpr)?.value ?: continue
      if (name == SEGMENT_COUNTER) segment = value
      if (name == LOGICAL_THREAD_ID && threadId != null) {
        if (value != threadId) return null
        guarded = true
      }
    }
    return segment?.let { it to guarded }
  }

  private fun simplifySegmentCounterUpdates(
    segmentVar: VarDecl<*>,
    labels: List<XcfaLabel>,
    passedSegmentValues: MutableSet<BigInteger>,
    segments: Segments,
  ): List<XcfaLabel> {
    val newLabels = mutableListOf<XcfaLabel>()
    // the labels below are simplified as if the edge were atomic, so at most one update is forced
    var forced = false
    labels.forEach { label ->
      val segmentUpdates = getSegmentUpdates(label)
      if (segmentUpdates.isNotEmpty()) {
        val next = segments.next(passedSegmentValues)
        val segmentUpdate = segmentUpdates.find { it.current.value == next }
        if (segmentUpdates.all { it.current.value in passedSegmentValues }) {
          // the counter is past every alternative: the update cannot fire
        } else if (segmentUpdate == null || forced) {
          newLabels.add(label)
        } else {
          forced = true
          passedSegmentValues.add(segmentUpdate.current.value)
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
          newLabels.add(AssignStmtLabel(segmentVar, segmentUpdate.next, segmentUpdate.metadata))
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
      } ?: emptyList()

  private fun simplifyStartLabelLogicalThread(
    label: XcfaLabel,
    passedSegmentValues: Set<BigInteger>,
    segments: Segments,
  ): List<XcfaLabel>? {
    if (label !is StartLabel) return null
    var assumption: AssumeStmt? = null
    val newParams =
      label.params.map { param ->
        var segmentCond: Expr<BoolType>? = null
        var nextSegmentAlternative: LitExpr<*>? = null
        val next = segments.next(passedSegmentValues)
        var expr = param
        while (expr is IteExpr<*>) {
          segmentIteValues<LitExpr<*>>(expr)?.let { (segmentValue, paramValue) ->
            if (segmentValue.value == next) {
              segmentCond = expr.cond
              nextSegmentAlternative = paramValue
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

  /**
   * [own] are the segments this procedure may fire, [unique] those of them no other label or thread
   * can fire. The next segment is the lowest own one not passed on the path, if it is sound to
   * force: when every lower segment is passed, or when it is [unique].
   */
  private class Segments(val own: Set<BigInteger>, val unique: Set<BigInteger>) {
    fun next(passed: Set<BigInteger>): BigInteger? =
      own.firstOrNull { it !in passed }?.takeIf { next -> next in unique || allBelow(passed, next) }

    private fun allBelow(passed: Set<BigInteger>, next: BigInteger): Boolean {
      var i = BigInteger.ZERO
      while (i < next) if (i++ !in passed) return false
      return true
    }
  }

  private inline fun <reified L : Expr<*>> segmentIteValues(e: IteExpr<*>): Pair<IntLitExpr, L>? {
    val eq = e.cond as? EqExpr<*> ?: return null
    if ((eq.leftOp as? RefExpr<*>)?.decl?.name != SEGMENT_COUNTER) return null
    val current = eq.rightOp as? IntLitExpr ?: return null
    val next = e.then as? L ?: return null
    return current to next
  }
}
