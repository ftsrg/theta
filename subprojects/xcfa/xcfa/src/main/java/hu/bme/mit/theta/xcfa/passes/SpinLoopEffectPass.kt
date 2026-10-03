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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.getInitLoops
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * Makes loop iterations that change nothing infeasible (dynamic spin-loop detection).
 *
 * An iteration that writes no global state and leaves every live local unchanged ends in the state
 * it started in, so dropping it loses no reachable state. Each loop gets an effect flag that is set
 * by every write that may change global state, and the back edges get `assume(flag || some live
 * local changed)`. A spinning iteration then cannot reach the next one, so a force-unrolled spin
 * loop no longer reaches its unroll exit and its safe result stays reliable.
 *
 * A write to a global variable or to memory counts only if it changes the stored value: the old
 * value is read and the new one written in one atomic block, and the flag is set when they differ.
 * So a failed compare-and-swap, which writes the old value back, or a repeated store of the same
 * value, counts as no effect. Every mutex, thread, call or other label always counts.
 *
 * Only for reachability: it removes spinning forever (termination), and it makes the checked writes
 * atomic (data races).
 */
class SpinLoopEffectPass(private val enabled: Boolean = true) : ProcedurePass {

  companion object {
    /** Off with --disable-spin-loop-effects. */
    var ENABLED = true

    private var counter = 0
  }

  private class Loop(
    val head: XcfaLocation,
    val edges: Set<XcfaEdge>,
    val backEdges: Set<XcfaEdge>,
    val entryEdges: Set<XcfaEdge>,
  ) {
    lateinit var effect: VarDecl<BoolType>
    val snapshots = mutableListOf<Pair<VarDecl<*>, VarDecl<*>>>()
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!enabled || !ENABLED) return builder
    val loops = findLoops(builder)
    if (loops.isEmpty()) return builder

    val globals = builder.parent.getVars().mapTo(mutableSetOf()) { it.wrappedVar }
    val live = strongLiveVars(builder)
    val instrumented =
      loops.filter { loop ->
        val written =
          loop.edges
            .flatMap { it.label.collectVarsWithAccessType().filter { a -> a.value.isWritten }.keys }
            .filter { it !in globals }
            .toSet()
        val liveWritten = written.filter { it in (live[loop.head] ?: emptySet()) }
        val id = counter++
        loop.effect = Decls.Var("__theta_spin_effect_$id", BoolType.getInstance())
        try {
          liveWritten.forEach { v ->
            val snap = Decls.Var("__theta_spin_snap_${id}_${v.name}", v.type)
            Neq(v.ref, snap.ref) // fails for types without equality: leave such loops alone
            loop.snapshots.add(v to snap)
          }
          true
        } catch (e: Exception) {
          false
        }
      }
    if (instrumented.isEmpty()) return builder
    instrumented.forEach { loop ->
      builder.addVar(loop.effect)
      loop.snapshots.forEach { builder.addVar(it.second) }
    }

    val loopsOf = mutableMapOf<XcfaEdge, MutableList<Loop>>()
    instrumented.forEach { loop ->
      loop.edges.forEach { loopsOf.getOrPut(it) { mutableListOf() }.add(loop) }
    }
    val backOf = mutableMapOf<XcfaEdge, MutableList<Loop>>()
    instrumented.forEach { loop ->
      loop.backEdges.forEach { backOf.getOrPut(it) { mutableListOf() }.add(loop) }
    }
    val entryOf = mutableMapOf<XcfaEdge, MutableList<Loop>>()
    instrumented.forEach { loop ->
      loop.entryEdges.forEach { entryOf.getOrPut(it) { mutableListOf() }.add(loop) }
    }

    val toRewrite = loopsOf.keys + entryOf.keys
    for (edge in toRewrite) {
      val enclosing = loopsOf[edge] ?: emptyList()
      val labels =
        if (enclosing.isEmpty()) edge.getFlatLabels().toMutableList()
        else
          instrumentEffects(edge.getFlatLabels(), enclosing, globals) { name, type ->
            Decls.Var("__theta_spin_${name}_${counter++}", type).also { builder.addVar(it) }
          }
      backOf[edge]?.forEach { loop ->
        val changed = loop.snapshots.map { (v, snap) -> Neq(v.ref, snap.ref) }
        labels.add(StmtLabel(Assume(Or(listOf(loop.effect.ref) + changed))))
        labels.addAll(reset(loop))
      }
      entryOf[edge]?.forEach { loop -> labels.addAll(reset(loop)) }
      builder.removeEdge(edge)
      builder.addEdge(
        XcfaEdge(
          edge.source,
          edge.target,
          SequenceLabel(labels, edge.label.metadata),
          edge.metadata,
        )
      )
    }
    return builder
  }

  private fun reset(loop: Loop): List<XcfaLabel> =
    listOf(AssignStmtLabel(loop.effect, Bool(false))) +
      loop.snapshots.map { (v, snap) -> AssignStmtLabel(snap, v.ref) }

  /**
   * Inserts the effect-flag updates of [loops] for the labels of an edge.
   *
   * A write to a global variable or to memory counts only if it changes the stored value: the new
   * value is computed first, then the old value is read and the cell written in one atomic block,
   * and the flag is set when they differ. Every other label that is not a plain local step (mutex
   * and thread operations, calls, havocs of globals, nondeterministic choices, ...) always counts.
   */
  private fun instrumentEffects(
    labels: List<XcfaLabel>,
    loops: List<Loop>,
    globals: Set<VarDecl<*>>,
    newVar: (String, Type) -> VarDecl<*>,
  ): MutableList<XcfaLabel> {
    val result = mutableListOf<XcfaLabel>()
    var inAtomic = false

    fun mark(condition: Expr<BoolType>?) {
      loops.forEach { loop ->
        val value = if (condition == null) Bool(true) else Or(loop.effect.ref, condition)
        result.add(AssignStmtLabel(loop.effect, value))
      }
    }

    /** `new := value; [old := cell; flag |= new != old; write(new)]` with the bracket atomic. */
    fun checkedWrite(cell: Expr<*>, value: Expr<*>, write: (Expr<*>) -> XcfaLabel) {
      val newValue = newVar("new", cell.type)
      val oldValue = newVar("old", cell.type)
      result.add(AssignStmtLabel(newValue, value))
      if (!inAtomic) result.add(AtomicBeginLabel())
      result.add(AssignStmtLabel(oldValue, cell))
      mark(Neq(newValue.ref, oldValue.ref))
      result.add(write(newValue.ref))
      if (!inAtomic) result.add(AtomicEndLabel())
    }

    for (label in labels) {
      when {
        label is AtomicBeginLabel -> inAtomic = true
        label is AtomicEndLabel -> inAtomic = false
        label is NopLabel -> {}
        label is StmtLabel -> {
          when (val stmt = label.stmt) {
            is AssumeStmt,
            is SkipStmt -> {}
            is MemoryAssignStmt<*, *, *> -> {
              checkedWrite(stmt.deref, stmt.expr) {
                StmtLabel(buildMemoryAssign(stmt.deref, it), metadata = label.metadata)
              }
              continue
            }
            is AssignStmt<*> ->
              if (stmt.varDecl in globals) {
                checkedWrite(stmt.varDecl.ref, stmt.expr) {
                  AssignStmtLabel(stmt.varDecl, it, label.metadata)
                }
                continue
              }
            is HavocStmt<*> -> if (stmt.varDecl in globals) mark(null)
            else -> mark(null)
          }
        }
        else -> mark(null) // mutex and thread operations, calls, returns, nondeterministic choices
      }
      result.add(label)
    }
    return result
  }

  /** Loops of the procedure by loop head; loops that can be entered elsewhere are left out. */
  private fun findLoops(builder: XcfaProcedureBuilder): List<Loop> =
    getInitLoops(builder.initLoc, builder.getEdges())
      .filterValues { it.isNotEmpty() }
      .map { (head, edges) ->
        val (inner, entries) = head.incomingEdges.partition { it in edges }
        Loop(head, edges, inner.toSet(), entries.toSet())
      }
}
