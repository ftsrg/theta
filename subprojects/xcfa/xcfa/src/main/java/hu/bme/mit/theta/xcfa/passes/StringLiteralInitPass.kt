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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferencesWithAccessType
import hu.bme.mit.theta.xcfa.utils.isRead

/**
 * Drops the character-by-character initialization of a string literal nothing ever reads.
 *
 * The frontend gives every string literal its own storage and fills it one cell per character, so a
 * program that merely prints its diagnostics pays a location and a memory write per character of
 * every message it can emit. That is most of the model in the string-heavy benchmarks, and none of
 * it is reachable by the property: the pointer is compared against null and handed to a library
 * stub, and no cell is ever read back.
 *
 * A literal keeps its initialization if any dereference *reads* one of its cells, or if the pointer
 * is stored into memory -- from where it could be loaded again and dereferenced through a base this
 * cannot recognize. Passing it to a call or assigning it to a variable is not enough on its own:
 * those keep the pointer syntactically visible, so a later content read still names this variable.
 *
 * Runs after inlining, where a read through a callee's parameter has become a read through this
 * variable.
 */
class StringLiteralInitPass : ProcedurePass {

  private var unread: Set<VarDecl<*>>? = null

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val dead = unread ?: unreadLiterals(builder.parent).also { unread = it }
    if (dead.isEmpty()) return builder
    builder.getEdges().toList().forEach { edge ->
      val stripped = edge.label.withoutInitOf(dead)
      if (stripped != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(stripped))
      }
    }
    return builder
  }

  private fun unreadLiterals(xcfa: XcfaBuilder): Set<VarDecl<*>> {
    val scan = Scan()
    xcfa.getProcedures().forEach { procedure ->
      procedure.getEdges().forEach { edge -> scan.visit(edge.label) }
    }
    return scan.droppable()
  }

  /**
   * What the whole program does with each string literal's address.
   *
   * The address reaches a read through a pointer variable, not through the literal itself, so the
   * flow has to be followed: `mayHold` says which literals a variable can hold, propagated over
   * assignments to a fixpoint, and any variable used as a dereference base keeps everything it can
   * hold.
   */
  private class Scan {
    val initialized = mutableSetOf<VarDecl<*>>()
    val readDirectly = mutableSetOf<VarDecl<*>>()
    val storedToMemory = mutableSetOf<VarDecl<*>>()
    val derefBases = mutableSetOf<VarDecl<*>>()
    val assignments = mutableListOf<Pair<VarDecl<*>, List<VarDecl<*>>>>()

    fun visit(label: XcfaLabel) {
      when (label) {
        is NondetLabel -> label.labels.forEach(::visit)
        is SequenceLabel -> label.labels.forEach(::visit)
        else -> {
          label.dereferencesWithAccessType.forEach { (deref, access) ->
            val vars = ExprUtils.getVars(deref.array)
            derefBases.addAll(vars)
            val root = (deref.array as? RefExpr<*>)?.decl as? VarDecl<*>
            if (root != null && root.isStringLiteral() && vars == setOf(root)) {
              if (access.isRead) readDirectly.add(root) else initialized.add(root)
            } else {
              readDirectly.addAll(vars.filter { it.isStringLiteral() })
            }
          }
          val stmt = (label as? StmtLabel)?.stmt
          if (stmt is MemoryAssignStmt<*, *, *>) {
            storedToMemory.addAll(ExprUtils.getVars(stmt.expr).filter { it.isStringLiteral() })
          }
          if (stmt is AssignStmt<*>) {
            assignments.add(stmt.varDecl to ExprUtils.getVars(stmt.expr).toList())
          }
        }
      }
    }

    fun droppable(): Set<VarDecl<*>> {
      val mayHold = mutableMapOf<VarDecl<*>, MutableSet<VarDecl<*>>>()
      var changed = true
      while (changed) {
        changed = false
        assignments.forEach { (target, sources) ->
          val holds = mayHold.getOrPut(target) { mutableSetOf() }
          val incoming =
            sources.flatMap { if (it.isStringLiteral()) listOf(it) else mayHold[it].orEmpty() }
          if (holds.addAll(incoming)) changed = true
        }
      }
      val keep = readDirectly + storedToMemory + derefBases.flatMap { mayHold[it].orEmpty() }
      return initialized - keep
    }
  }

  private fun XcfaLabel.withoutInitOf(dead: Set<VarDecl<*>>): XcfaLabel =
    when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.withoutInitOf(dead) }, metadata)
      is StmtLabel -> {
        val assign = stmt as? MemoryAssignStmt<*, *, *>
        val base = (assign?.deref?.array as? RefExpr<*>)?.decl as? VarDecl<*>
        if (base != null && base in dead) NopLabel else this
      }

      else -> this
    }
}

/** The frontend names each string literal's storage `__theta_str<n>`. */
private val STRING_LITERAL_NAME = Regex("""__theta_str\d+$""")

private fun VarDecl<*>.isStringLiteral() = STRING_LITERAL_NAME.containsMatchIn(name)
