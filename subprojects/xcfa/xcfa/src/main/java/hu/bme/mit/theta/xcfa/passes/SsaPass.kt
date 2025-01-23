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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.IndexedVarDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.model.*

/** Transform the procedure to Static Single Assignment (SSA) form. */
class SSAPass : ProcedurePass {

  private val ssaUtils = SSAUtils()

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(ssaUtils.toSSA(edge)))
    }
    return builder
  }
}

internal class SSAUtils {

  private var indexing: VarIndexing = VarIndexingFactory.indexing(0)

  private val indexedVars = mutableSetOf<VarDecl<*>>()

  fun toSSA(edge: XcfaEdge) = edge.label.toSSA()

  fun removeSSA(edge: XcfaEdge) = edge.withLabel(edge.label.removeSSA())

  // Convert to SSA

  private fun XcfaLabel.toSSA(): XcfaLabel {
    return when (this) {
      is StmtLabel -> {
        when (val stmt = this.stmt) {
          is AssignStmt<*> -> StmtLabel(stmt.toSSA(), choiceType, metadata)
          is AssumeStmt -> StmtLabel(stmt.toSSA(), choiceType, metadata)
          is HavocStmt<*> -> StmtLabel(stmt.toSSA(), choiceType, metadata)
          else -> error("Unsupported statement at SSA conversion: $stmt")
        }
      }

      is StartLabel ->
        StartLabel(name, params.map { it.toSSA() }, pidVar.getIndexed(), metadata, tempLookup)
      is JoinLabel -> JoinLabel(pidVar.getIndexed(), metadata)
      is SequenceLabel -> SequenceLabel(labels.map { it.toSSA() }, metadata)
      is NopLabel,
      is FenceLabel -> this
      else -> error("Unsupported label at SSA conversion: $this")
    }
  }

  private fun <T : Type> Expr<T>.toSSA(): Expr<T> {
    val unfolded = toSSAAtomic()
    ExprUtils.getVars(this).forEach { indexing = indexing.inc(it) }
    return unfolded
  }

  private fun <T : Type> Expr<T>.toSSAAtomic(): Expr<T> =
    if (this is RefExpr<T>) {
      (decl as? VarDecl<T>)?.getIndexed(false)?.ref ?: this
    } else {
      map { it.toSSAAtomic() }
    }

  private fun <T : Type> VarDecl<T>.getIndexed(increment: Boolean = true): VarDecl<T> {
    val newName = this.name + "#" + indexing[this]
    indexedVars
      .find { it.name == newName }
      ?.let {
        return it as VarDecl<T>
      }
    val newVar = IndexedVarDecl.of(newName, this)
    indexedVars.add(newVar)
    if (increment) indexing = indexing.inc(this)
    return newVar
  }

  private fun <T : Type> AssignStmt<T>.toSSA() = AssignStmt.of(varDecl.getIndexed(), expr.toSSA())

  private fun AssumeStmt.toSSA() = AssumeStmt.of(cond.toSSA())

  private fun <T : Type> HavocStmt<T>.toSSA() = HavocStmt.of(varDecl.getIndexed())

  // Remove SSA

  private fun XcfaLabel.removeSSA(): XcfaLabel {
    return when (this) {
      is StmtLabel -> {
        when (val stmt = this.stmt) {
          is AssignStmt<*> -> StmtLabel(stmt.removeSSA(), choiceType, metadata)
          is AssumeStmt -> StmtLabel(stmt.removeSSA(), choiceType, metadata)
          is HavocStmt<*> -> StmtLabel(stmt.removeSSA(), choiceType, metadata)
          else -> this
        }
      }

      is StartLabel ->
        StartLabel(name, params.map { it.removeSSA() }, pidVar.noindex, metadata, tempLookup)
      is JoinLabel -> JoinLabel(pidVar.noindex, metadata)
      is SequenceLabel -> SequenceLabel(labels.map { it.removeSSA() }, metadata)
      else -> this
    }
  }

  private fun <T : Type> Expr<T>.removeSSA(): Expr<T> =
    if (this is RefExpr<T>) {
      ((decl as? IndexedVarDecl)?.original ?: decl).ref
    } else {
      map { it.removeSSA() }
    }

  private val <T : Type> VarDecl<T>.noindex
    get() = (this as? IndexedVarDecl)?.original ?: this

  private fun <T : Type> AssignStmt<T>.removeSSA() =
    AssignStmt.of(varDecl.noindex, expr.removeSSA())

  private fun AssumeStmt.removeSSA() = AssumeStmt.of(cond.removeSSA())

  private fun <T : Type> HavocStmt<T>.removeSSA() = HavocStmt.of(varDecl.noindex)
}
