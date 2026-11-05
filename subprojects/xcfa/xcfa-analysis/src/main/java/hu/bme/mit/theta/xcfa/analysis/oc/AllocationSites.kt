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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.MemoryAssign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * Gives each allocation of constant size a fixed address under flat addressing. An unrolled thread
 * runs an allocation at most once, so addresses from a counter private to the event graph are as
 * distinct as those of the shared counter, whose concurrent reads would make them unknown to
 * [XcfaOcValueAnalysis]. Applies only if the program uses the counter for nothing else; memory
 * safety checks do, as they bound addresses by it.
 */
internal class AllocationSites(xcfa: XCFA, private val parseContext: ParseContext) : ProcedurePass {

  private val pointerType = CPointer(null, null, parseContext)

  private val counter: VarDecl<*>? =
    xcfa.globalVars.map { it.wrappedVar }.find { it.name == COUNTER_NAME }

  private val enabled: Boolean

  private var next: BigInteger

  init {
    var highest =
      if (parseContext.memoryModel.flatAddressing()) parseContext.flatAddressSpace.end()
      else BigInteger.ZERO
    val labels = xcfa.procedures.flatMap { p -> p.edges.map { it.getFlatLabels() } }
    enabled =
      counter != null &&
        parseContext.memoryModel.flatAddressing() &&
        !parseContext.isCheckMemsafety &&
        labels.all { edge ->
          var i = 0
          while (i < edge.size) {
            val length = siteLength(edge, i)
            if (length > 0) {
              i += length
              continue
            }
            val literal = initialValue(edge[i])
            if (literal != null) highest = highest.max(literal)
            else if (counter in edge[i].collectVars()) return@all false
            i++
          }
          true
        }
    next = highest
  }

  /** Runs on the copy of a procedure for one thread, so that each thread has its own addresses. */
  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!enabled) return builder
    builder.getEdges().toList().forEach { edge ->
      val labels = edge.getFlatLabels()
      val rewritten = rewrite(labels)
      if (rewritten.size != labels.size) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(rewritten, edge.label.metadata)))
      }
    }
    return builder
  }

  /** [labels], with each allocation replaced by the assignment of its fixed address. */
  private fun rewrite(labels: List<XcfaLabel>): List<XcfaLabel> {
    val result = ArrayList<XcfaLabel>(labels.size)
    var i = 0
    while (i < labels.size) {
      val length = siteLength(labels, i)
      if (length == 0) {
        result.add(labels[i++])
        continue
      }
      result.add(assignAddress(labels[i], next))
      next += extent(labels[i + 1])!!
      i += length
    }
    return result
  }

  /** The number of labels of the allocation starting at index [i], or 0 if there is none. */
  private fun siteLength(labels: List<XcfaLabel>, i: Int): Int {
    if (i + 1 >= labels.size || !readsCounter(labels[i]) || extent(labels[i + 1]) == null) return 0
    val assume = (labels.getOrNull(i + 2) as? StmtLabel)?.stmt as? AssumeStmt
    return if (assume != null && counter in ExprUtils.getVars(assume.cond)) 3 else 2
  }

  private fun readsCounter(label: XcfaLabel): Boolean =
    when (val stmt = (label as? StmtLabel)?.stmt) {
      is AssignStmt<*> -> isCounter(stmt.expr) && stmt.varDecl != counter
      is MemoryAssignStmt<*, *, *> -> isCounter(stmt.expr)
      else -> false
    }

  private fun isCounter(expr: Expr<*>): Boolean =
    counter != null && ExprUtils.getVars(expr) == setOf(counter) && expr.ops.size <= 1

  /** How much `__malloc = __malloc + extent` adds, if that is what [label] is. */
  private fun extent(label: XcfaLabel): BigInteger? {
    val stmt = (label as? StmtLabel)?.stmt as? AssignStmt<*> ?: return null
    if (stmt.varDecl != counter || counter!! !in ExprUtils.getVars(stmt.expr)) return null
    val zero = pointerType.nullValue
    val valuation = ImmutableValuation.builder().put(counter, zero).build()
    return value(ExprUtils.simplify(stmt.expr, valuation))
  }

  private fun initialValue(label: XcfaLabel): BigInteger? {
    val stmt = (label as? StmtLabel)?.stmt as? AssignStmt<*> ?: return null
    return if (stmt.varDecl == counter) value(ExprUtils.simplify(stmt.expr)) else null
  }

  private fun value(expr: Expr<*>): BigInteger? =
    when (expr) {
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(expr)
      is IntLitExpr -> expr.value
      else -> null
    }

  private fun assignAddress(label: XcfaLabel, address: BigInteger): XcfaLabel {
    val literal: LitExpr<*> = pointerType.getValue(address.toString())
    val stmt = (label as StmtLabel).stmt
    return when (stmt) {
      is AssignStmt<*> ->
        label.copy(
          stmt = Assign(cast(stmt.varDecl, stmt.varDecl.type), cast(literal, stmt.varDecl.type))
        )
      is MemoryAssignStmt<*, *, *> ->
        @Suppress("UNCHECKED_CAST")
        label.copy(
          stmt =
            MemoryAssign(
              stmt.deref as Dereference<Type, Type, Type>,
              cast(literal, stmt.deref.type) as Expr<Type>,
            )
        )
      else -> error("Not an allocation: $label")
    }
  }

  private companion object {
    const val COUNTER_NAME = "__malloc"
  }
}
