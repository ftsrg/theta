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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.utils.collectHavocs
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * True if the Unsafe verdict with [cex] may depend on a value that [XCFA.overApproximatedVars]
 * lists, so that the counterexample may not exist in C. Without an XCFA trace to slice, any such
 * havoc left in the model counts.
 */
fun unsafeDependsOnOverApproximation(cex: Cex?, xcfa: XCFA): Boolean {
  val recorded = xcfa.overApproximatedVars
  if (recorded.isEmpty()) return false
  val trace = cex as? Trace<*, *>
  if (trace != null && trace.actions.isNotEmpty() && trace.actions.all { it is XcfaAction }) {
    // The analysis renames the locals of each process, and its labels name these instances. Names
    // identify them: equal instances are not always the same object.
    val byName = recorded.mapKeys { it.key.name }.toMutableMap()
    val scratch = xcfa.overApproximationScratchVars
    val scratchNames = scratch.map { it.name }.toMutableSet()
    trace.states.forEach { state ->
      (state as? XcfaState<*>)?.processes?.values?.forEach { process ->
        process.varLookup.forEach { frame ->
          frame.forEach { (original, instance) ->
            if (original in recorded) byName[instance.name] = recorded[original]
            if (original in scratch) scratchNames += instance.name
          }
        }
      }
    }
    // An assumption over scratch variables alone, one of them recorded, is a fact of the pass.
    val isFact: (Expr<BoolType>) -> Boolean = { cond ->
      val names = ExprUtils.getVars(cond).map { it.name }
      names.any { it in byName } && names.all { it in scratchNames }
    }
    return dependsOnOverApproximation(
      trace.actions.flatMap { (it as XcfaAction).label.getFlatLabels() },
      byName,
      isFact,
    )
  }
  return (xcfa.procedures + xcfa.initProcedures.map { it.first }).any { procedure ->
    procedure.edges.any { edge -> edge.label.collectHavocs().any { it.varDecl in recorded.keys } }
  }
}

/**
 * A backward slice of the trace [labels], from every assumption through the assignments to the
 * variables they read. Memory counts as one location: a read in the slice adds every earlier write.
 * If no havoc of a variable named in [recorded] is in the slice, the trace is feasible for every
 * value of those variables, thus also for the value that the real call gives.
 *
 * An assumption that holds for every value of the C type of such a variable (the range that the
 * passes state after its havoc) is not in the slice: the real value satisfies it too. [recorded]
 * maps the variable names to these intervals. Neither is an assumption that [isFact] accepts (see
 * [XCFA.overApproximationScratchVars]): the real value satisfies it whatever its other variables
 * hold.
 */
internal fun dependsOnOverApproximation(
  labels: List<XcfaLabel>,
  recorded: Map<String, ClosedRange<BigInteger>?>,
  isFact: (Expr<BoolType>) -> Boolean = { false },
): Boolean {
  val relevant = mutableSetOf<String>()
  var memoryRelevant = false
  for (i in labels.indices.reversed()) {
    val label = labels[i]
    when (val stmt = (label as? StmtLabel)?.stmt) {
      is AssumeStmt ->
        if (!holdsForTheType(stmt.cond, recorded) && !isFact(stmt.cond)) {
          relevant += ExprUtils.getVars(stmt.cond).map { it.name }
          if (stmt.cond.dereferences.isNotEmpty()) memoryRelevant = true
        }
      is AssignStmt<*> ->
        if (stmt.varDecl.name in relevant) {
          relevant += ExprUtils.getVars(stmt.expr).map { it.name }
          if (stmt.expr.dereferences.isNotEmpty()) memoryRelevant = true
        }
      is HavocStmt<*> ->
        if (stmt.varDecl.name in relevant && stmt.varDecl.name in recorded) return true
      is MemoryAssignStmt<*, *, *> ->
        if (memoryRelevant) {
          relevant += StmtUtils.getVars(stmt).map { it.name }
        }
      is SkipStmt -> {}
      else -> {
        if (label is NopLabel) continue
        // Not a plain statement: every variable it touches counts, and a recorded one decides.
        val vars = label.collectVars().map { it.name }
        if (vars.any { it in recorded }) return true
        relevant += vars
        if (label.dereferences.isNotEmpty()) memoryRelevant = true
      }
    }
  }
  return false
}

/** True for `lo <= v && v <= hi` where `[lo, hi]` contains the whole C type interval of `v`. */
private fun holdsForTheType(
  cond: Expr<BoolType>,
  recorded: Map<String, ClosedRange<BigInteger>?>,
): Boolean {
  val ops = (cond as? AndExpr)?.ops ?: return false
  if (ops.size != 2) return false
  val lower = ops[0] as? GeqExpr<*> ?: return false
  val upper = ops[1] as? LeqExpr<*> ?: return false
  val name = ((lower.leftOp as? RefExpr<*>)?.decl ?: return false).name
  if (((upper.leftOp as? RefExpr<*>)?.decl ?: return false).name != name) return false
  val lo = (lower.rightOp as? IntLitExpr)?.value ?: return false
  val hi = (upper.rightOp as? IntLitExpr)?.value ?: return false
  val range = recorded[name] ?: return false
  return lo <= range.start && hi >= range.endInclusive
}
