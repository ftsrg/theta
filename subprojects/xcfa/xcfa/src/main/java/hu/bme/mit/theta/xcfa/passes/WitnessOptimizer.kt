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
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.LAST_SEGMENT_PASSED
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.intersect
import hu.bme.mit.theta.xcfa.utils.simplify

/**
 * Prepares the witness instrumentation of one thread for the OC backend.
 *
 * Literal input parameters (e.g., the logical thread id handed over by the spawning thread) are
 * propagated through the procedure, keeping only values that agree on all incoming edges at joins,
 * which drops the instrumentation meant for other threads. Every remaining guarded update of the
 * segment counter or the last-segment flag, and every guarded thread-id hand-over, is then split
 * into one branch per alternative plus a fall-through: the shared counter is written only when a
 * segment is actually passed, and no alternative is ruled out.
 */
class WitnessOptimizer(private val params: List<Expr<*>>, private val parseContext: ParseContext) :
  ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val witnessVars =
      builder
        .getEdges()
        .flatMap { edge -> edge.label.getFlatLabels().flatMap { it.collectVars() } }
        .filter { it.name == SEGMENT_COUNTER || it.name == LAST_SEGMENT_PASSED }
        .toSet()
    // without a witness being validated there is no instrumentation
    if (witnessVars.none { it.name == SEGMENT_COUNTER }) return builder

    propagateParams(builder, witnessVars)
    builder.getEdges().toList().forEach { splitAlternatives(builder, it, witnessVars) }
    return builder
  }

  private fun propagateParams(builder: XcfaProcedureBuilder, witnessVars: Set<VarDecl<*>>) {
    val initialValuation = MutableValuation()
    builder.getParams().forEachIndexed { index, param ->
      if (param.second == ParamDirection.IN && index < params.size && params[index] is LitExpr<*>) {
        initialValuation.put(param.first, params[index] as LitExpr<*>)
      }
    }
    val globals = builder.parent.getVars().map { it.wrappedVar }

    val waitlist =
      mutableMapOf(builder.initLoc to mutableListOf<MutableValuation>(initialValuation))
    while (waitlist.isNotEmpty()) {
      val (loc, valuations) =
        waitlist.firstNotNullOf { (loc, valuations) ->
          if (valuations.size >= loc.incomingEdges.size) loc to valuations else null
        }
      waitlist.remove(loc)
      val merged = valuations.drop(1).fold(valuations.first() as Valuation, ::intersect)

      loc.outgoingEdges.toList().forEach { edge ->
        val valuation = MutableValuation.copyOf(merged)
        val oldLabels = edge.getFlatLabels()
        val newLabels =
          oldLabels
            .map { it.simplify(valuation, parseContext) }
            .filterNot { it.isTrivial(witnessVars) }
        globals.forEach { valuation.remove(it) }
        if (newLabels != oldLabels) {
          builder.removeEdge(edge)
          builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
        }
        waitlist.getOrPut(edge.target) { mutableListOf() }.add(valuation)
      }
    }
  }

  private fun splitAlternatives(
    builder: XcfaProcedureBuilder,
    edge: XcfaEdge,
    witnessVars: Set<VarDecl<*>>,
  ) {
    val labels = edge.getFlatLabels()
    val alternatives = labels.map { it.alternatives(witnessVars) }
    val lastSplit = alternatives.indexOfLast { it != null }
    if (lastSplit == -1) return

    builder.removeEdge(edge)
    var source = edge.source
    val pending = mutableListOf<XcfaLabel>()
    fun newLoc() =
      XcfaLocation("__loc_witness_" + XcfaLocation.uniqueCounter(), metadata = EmptyMetaData)
    labels.forEachIndexed { index, label ->
      val branches = alternatives[index]
      if (branches == null) {
        pending.add(label)
        return@forEachIndexed
      }
      if (pending.isNotEmpty()) {
        val loc = newLoc()
        builder.addEdge(XcfaEdge(source, loc, SequenceLabel(pending.toList()), edge.metadata))
        source = loc
        pending.clear()
      }
      val join = if (index == labels.size - 1) edge.target else newLoc()
      branches.forEach { (cond, branchLabels) ->
        val guard = StmtLabel(Assume(cond), ChoiceType.NONE, EmptyMetaData)
        builder.addEdge(
          XcfaEdge(source, join, SequenceLabel(listOf(guard) + branchLabels), edge.metadata)
        )
      }
      source = join
    }
    if (source != edge.target) {
      builder.addEdge(XcfaEdge(source, edge.target, SequenceLabel(pending.toList()), edge.metadata))
    }
  }

  /**
   * The alternatives of a guarded witness update as (condition, labels) pairs, the fall-through
   * last; null if the label is not such an update.
   */
  private fun XcfaLabel.alternatives(
    witnessVars: Set<VarDecl<*>>
  ): List<Pair<Expr<BoolType>, List<XcfaLabel>>>? =
    when {
      this is StmtLabel && stmt is AssignStmt<*> && stmt.varDecl in witnessVars -> {
        val v = stmt.varDecl
        cases(stmt.expr) { value ->
          if (value is RefExpr<*> && value.decl == v) listOf()
          else listOf(AssignStmtLabel(v, value, metadata))
        }
      }
      else -> null
    }

  private fun cases(
    expr: Expr<*>,
    labelsOf: (Expr<*>) -> List<XcfaLabel>,
  ): List<Pair<Expr<BoolType>, List<XcfaLabel>>>? {
    if (expr !is IteExpr<*>) return null
    val result = mutableListOf<Pair<Expr<BoolType>, List<XcfaLabel>>>()
    val previous = mutableListOf<Expr<BoolType>>()
    var e: Expr<*> = expr
    while (e is IteExpr<*>) {
      result.add(ExprUtils.simplify(And(previous.map { Not(it) } + e.cond)) to labelsOf(e.then))
      previous.add(e.cond)
      e = e.`else`
    }
    result.add(ExprUtils.simplify(And(previous.map { Not(it) })) to labelsOf(e))
    return result.filter { it.first != False() }
  }

  private fun XcfaLabel.isTrivial(witnessVars: Set<VarDecl<*>>): Boolean =
    this is StmtLabel &&
      when (stmt) {
        is AssignStmt<*> ->
          stmt.varDecl in witnessVars && (stmt.expr as? RefExpr<*>)?.decl == stmt.varDecl
        is AssumeStmt -> stmt.cond == True() && choiceType == ChoiceType.NONE
        else -> false
      }
}
