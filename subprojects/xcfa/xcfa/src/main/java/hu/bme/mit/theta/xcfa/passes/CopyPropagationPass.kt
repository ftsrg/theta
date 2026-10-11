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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * Forwards copies, so that the temporaries carrying a value (call results, return values, copied
 * parameters) are no longer read and [UnusedVarPass] can remove them.
 *
 * Within an edge, a read of a local assigned earlier in the same edge becomes the assigned
 * expression. Across edges, a read of a local `y` becomes `t` where every path last did `y := t`
 * with `t` a local not written since; other threads never touch locals, so this holds between edges
 * too. Literals are left to [SimplifyExprsPass].
 */
class CopyPropagationPass : ProcedurePass {

  companion object {
    /** Larger expressions are not copied into their uses. */
    private const val MAX_SIZE = 40
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val locals = builder.getVars().toSet() - builder.getParams().map { it.first }.toSet()
    copyPropagation(builder, locals)
    builder.getEdges().toList().forEach { edge ->
      val labels = flatten(edge.label)
      val propagated = propagate(labels, locals)
      if (propagated != labels) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(propagated, edge.label.metadata)))
      }
    }
    return builder
  }

  /**
   * Replaces a read of a local `y` by `t` where every path last did `y := t` with `t` a local not
   * written since. Other threads never touch locals, so this holds across edges too; chains of
   * copies (a result handed back through several calls) collapse to the local that holds the value.
   */
  private fun copyPropagation(builder: XcfaProcedureBuilder, locals: Set<VarDecl<*>>) {
    fun kill(copies: MutableMap<VarDecl<*>, VarDecl<*>>, v: VarDecl<*>) {
      copies.remove(v)
      copies.entries.removeIf { it.value == v }
    }
    fun transfer(copies: MutableMap<VarDecl<*>, VarDecl<*>>, label: XcfaLabel) {
      val st = (label as? StmtLabel)?.stmt
      when (st) {
        is AssignStmt<*> -> {
          kill(copies, st.varDecl)
          val src = (st.expr as? RefExpr<*>)?.decl as? VarDecl<*>
          if (st.varDecl in locals && src != null && src in locals && src != st.varDecl)
            copies[st.varDecl] = copies[src] ?: src
        }
        is AssumeStmt,
        is MemoryAssignStmt<*, *, *> -> {}
        else ->
          label
            .collectVarsWithAccessType()
            .filter { it.value.isWritten }
            .keys
            .forEach { kill(copies, it) }
      }
    }
    val at = mutableMapOf<XcfaLocation, Map<VarDecl<*>, VarDecl<*>>>(builder.initLoc to emptyMap())
    val work = ArrayDeque(listOf(builder.initLoc))
    while (work.isNotEmpty()) {
      val loc = work.removeFirst()
      for (e in loc.outgoingEdges) {
        val out = at[loc]!!.toMutableMap()
        flatten(e.label).forEach { transfer(out, it) }
        val old = at[e.target]
        val joined = if (old == null) out else old.filter { (v, t) -> out[v] == t }
        if (joined != old) {
          at[e.target] = joined
          if (e.target !in work) work.addLast(e.target)
        }
      }
    }
    builder.getEdges().toList().forEach { edge ->
      val copies = (at[edge.source] ?: return@forEach).toMutableMap()
      val labels = flatten(edge.label)
      val newLabels =
        labels.map { label ->
          val replaced =
            if (copies.isEmpty()) label else substLabel(label, copies.mapValues { it.value.ref })
          transfer(copies, replaced)
          replaced
        }
      if (newLabels != labels) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(newLabels, edge.label.metadata)))
      }
    }
  }

  private fun substLabel(label: XcfaLabel, map: Map<VarDecl<*>, Expr<*>>): XcfaLabel {
    val st = (label as? StmtLabel)?.stmt ?: return label
    val newStmt =
      when (st) {
        is AssignStmt<*> ->
          AssignStmt.of(
            cast(st.varDecl, st.varDecl.type),
            cast(st.expr.subst(map), st.varDecl.type),
          )
        is AssumeStmt -> AssumeStmt.of(st.cond.subst(map))
        is MemoryAssignStmt<*, *, *> ->
          MemoryAssignStmt.create(st.deref.subst(map) as Dereference<*, *, *>, st.expr.subst(map))
        else -> return label
      }
    return if (newStmt == st) label else StmtLabel(newStmt, label.choiceType, label.metadata)
  }

  private fun flatten(label: XcfaLabel): List<XcfaLabel> =
    if (label is SequenceLabel) label.labels.flatMap { flatten(it) } else listOf(label)

  private fun size(e: Expr<*>): Int = 1 + e.ops.sumOf { size(it) }

  private fun hasDeref(e: Expr<*>): Boolean =
    e is Dereference<*, *, *> || e.ops.any { hasDeref(it) }

  private fun <T : Type> Expr<T>.subst(map: Map<VarDecl<*>, Expr<*>>): Expr<T> {
    if (this is RefExpr<*>)
      map[decl]?.let {
        return cast(it, type)
      }
    if (ops.isEmpty()) return this
    return withOps(ops.map { it.subst(map) })
  }

  private fun propagate(labels: List<XcfaLabel>, locals: Set<VarDecl<*>>): List<XcfaLabel> {
    val map = mutableMapOf<VarDecl<*>, Expr<*>>()
    fun kill(v: VarDecl<*>) {
      map.remove(v)
      map.entries.removeIf { (_, e) -> v in ExprUtils.getVars(e) }
    }
    return labels.map { label ->
      val st = (label as? StmtLabel)?.stmt
      when (st) {
        is AssignStmt<*> -> {
          val e = st.expr.subst(map)
          kill(st.varDecl)
          if (
            st.varDecl in locals &&
              !hasDeref(e) &&
              st.varDecl !in ExprUtils.getVars(e) &&
              size(e) <= MAX_SIZE
          )
            map[st.varDecl] = e
          StmtLabel(
            AssignStmt.of(cast(st.varDecl, st.varDecl.type), cast(e, st.varDecl.type)),
            label.choiceType,
            label.metadata,
          )
        }
        is AssumeStmt ->
          StmtLabel(AssumeStmt.of(st.cond.subst(map)), label.choiceType, label.metadata)
        is MemoryAssignStmt<*, *, *> ->
          StmtLabel(
            MemoryAssignStmt.create(
              st.deref.subst(map) as Dereference<*, *, *>,
              st.expr.subst(map),
            ),
            label.choiceType,
            label.metadata,
          )
        is HavocStmt<*> -> {
          kill(st.varDecl)
          label
        }
        else -> {
          label.collectVarsWithAccessType().filter { it.value.isWritten }.keys.forEach { kill(it) }
          label
        }
      }
    }
  }
}
