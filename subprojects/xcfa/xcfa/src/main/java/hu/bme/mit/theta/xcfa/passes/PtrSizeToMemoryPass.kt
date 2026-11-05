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
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import java.math.BigInteger

/**
 * Stores the memsafety ghost arrays in memory, which lets solvers without arrays check memory
 * safety. Under multi, `size[k]` is the cell at offset `k` of the null object, which no checked
 * access can reach; under flat, where all program memory has base 0, each array gets a base of its
 * own.
 *
 * A cell nothing wrote reads 0, the arrays' default; the OC encoding is what provides that (see
 * [isGhostCell]), so this pass is for that backend only.
 *
 * Under flat, constant writes to static addresses on the entry path of the init procedure describe
 * static objects, which later code only overwrites on a path that has already failed the check.
 * They become a table in the reads, as each would otherwise be a read-from candidate of every
 * symbolic read.
 */
class PtrSizeToMemoryPass(private val parseContext: ParseContext) : ProcedurePass {

  companion object {
    var enabled = false
    private var bases: Set<Expr<*>> = emptySet()
    private const val CENSUS_KEY = "ghostArrayCensus"

    /** Whether a dereference of [array] accesses a ghost array, whose unwritten cells read 0. */
    fun isGhostCell(array: Expr<*>?): Boolean = enabled && array != null && array in bases
  }

  private val pointerType = CPointer(null, null, parseContext)

  /** Collected once per XCFA, as passes rewrite procedures one by one. */
  private class Census(
    val tables: Map<VarDecl<ArrayType<*, *>>, Map<LitExpr<*>, LitExpr<*>>>,
    val tableLabels: Set<XcfaLabel>,
    val dynamicWrites: Set<VarDecl<*>>,
  )

  private lateinit var census: Census

  private fun takeCensus(xcfa: XcfaBuilder, ghosts: Set<VarDecl<ArrayType<*, *>>>): Census {
    val found = ghosts.associateWith { mutableMapOf<LitExpr<*>, LitExpr<*>>() }
    val entryLabels = mutableSetOf<XcfaLabel>()
    val flat = parseContext.memoryModel == ArchitectureConfig.MemoryModelType.flat
    val staticEnd = parseContext.flatAddressSpace.end().takeIf { flat }
    if (flat)
      xcfa.getInitProcedures().forEach { (init, _) ->
        var loc = init.initLoc
        val seen = mutableSetOf(loc)
        while (loc.outgoingEdges.size == 1) {
          val edge = loc.outgoingEdges.first()
          edge.getFlatLabels().forEach { label ->
            val assign = (label as? StmtLabel)?.stmt as? AssignStmt<*>
            val cells = found[assign?.varDecl]
            val constant = assign?.expr?.constantCells(assign.varDecl)
            if (
              cells != null && constant != null && constant.keys.all { it.isBelow(staticEnd!!) }
            ) {
              cells.putAll(constant)
              entryLabels.add(label)
            }
          }
          loc = edge.target
          if (!seen.add(loc)) break
        }
      }
    val dynamicWrites =
      xcfa
        .getProcedures()
        .flatMap { it.getEdges() }
        .flatMap { it.getFlatLabels() }
        .filter { it !in entryLabels }
        .flatMap { label -> label.collectVarsWithAccessType().filter { it.value.isWritten }.keys }
        .filter { it in ghosts }
        .toSet()
    return Census(found, entryLabels, dynamicWrites)
  }

  private fun LitExpr<*>.isBelow(end: BigInteger): Boolean =
    when (this) {
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this) < end
      is IntLitExpr -> value < end
      else -> false
    }

  /** The cells [this] sets on top of [ghost]'s old value, or null if one is not constant. */
  internal fun Expr<*>.constantCells(ghost: VarDecl<*>): Map<LitExpr<*>, LitExpr<*>>? =
    when {
      this == ghost.ref -> emptyMap()
      this is ArrayLitExpr<*, *> ->
        elements
          .map { it.get1() as? LitExpr<*> to it.get2() as? LitExpr<*> }
          .takeIf { c -> c.all { it.first != null && it.second != null } }
          ?.associate { it.first!! to it.second!! }
      this is ArrayWriteExpr<*, *> -> {
        val key = index as? LitExpr<*>
        val value = elem as? LitExpr<*>
        if (key == null || value == null) null else array.constantCells(ghost)?.plus(key to value)
      }
      else -> null
    }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!enabled || !parseContext.isCheckMemsafety) return builder
    val ghosts: Map<VarDecl<ArrayType<*, *>>, Expr<*>> =
      when (parseContext.memoryModel) {
        ArchitectureConfig.MemoryModelType.multi ->
          mapOf(builder.parent.getPtrSizeVar() to pointerType.nullValue)
        ArchitectureConfig.MemoryModelType.flat ->
          listOfNotNull(
              builder.parent.getPtrSizeVar(),
              builder.parent.getObjExtentVar(),
              builder.parent.getObjHeapVar(),
            )
            .withIndex()
            .associate { (i, ghost) -> ghost to pointerType.getValue("${i + 1}") }
        else -> error("The memsafety ghosts cannot be stored in memory under this memory model")
      }
    bases = ghosts.values.toSet()
    census =
      builder.parent.metaData.getOrPut(CENSUS_KEY) { takeCensus(builder.parent, ghosts.keys) }
        as Census
    builder.getEdges().toList().forEach { edge ->
      builder.removeEdge(edge)
      builder.addEdge(
        edge.withLabel(SequenceLabel(edge.label.rewrite(ghosts), edge.label.metadata))
      )
    }
    return builder
  }

  private fun XcfaLabel.rewrite(ghosts: Map<VarDecl<ArrayType<*, *>>, Expr<*>>): List<XcfaLabel> =
    when (this) {
      is SequenceLabel -> labels.flatMap { it.rewrite(ghosts) }
      is NondetLabel ->
        listOf(
          NondetLabel(
            labels.map { SequenceLabel(it.rewrite(ghosts), it.metadata) }.toSet(),
            metadata,
          )
        )
      is StmtLabel -> {
        val ghost = (stmt as? AssignStmt<*>)?.varDecl?.let { v -> ghosts.keys.find { it == v } }
        if (ghost != null && this in census.tableLabels) listOf()
        else if (ghost != null)
          (stmt as AssignStmt<*>).expr.writes(ghost, ghosts).map {
            StmtLabel(it, choiceType, metadata)
          }
        else listOf(StmtLabel(stmt.rewrite(ghosts), choiceType, metadata))
      }
      else -> {
        check(ghosts.keys.none { it in collectVars() }) { "Unsupported use of a ghost in $this" }
        listOf(this)
      }
    }

  private fun Stmt.rewrite(ghosts: Map<VarDecl<ArrayType<*, *>>, Expr<*>>): Stmt =
    when (this) {
      is AssumeStmt -> AssumeStmt.of(cast(cond.rewrite(ghosts), cond.type))
      is AssignStmt<*> -> {
        check(varDecl.type !is ArrayType<*, *>) { "Unsupported assignment of $varDecl" }
        AssignStmt.of(cast(varDecl, varDecl.type), cast(expr.rewrite(ghosts), varDecl.type))
      }
      is MemoryAssignStmt<*, *, *> ->
        MemoryAssignStmt.of(
          deref.rewrite(ghosts) as Dereference<Type, Type, Type>,
          cast(expr.rewrite(ghosts), deref.type),
        )
      is HavocStmt<*> -> {
        check(varDecl !in ghosts.keys) { "Unsupported havoc of $varDecl" }
        this
      }
      is SkipStmt -> this
      else -> error("Unsupported statement next to the ghosts: $this")
    }

  /** The simplifier may have folded the array's current value into [this]: it can be a literal. */
  private fun Expr<*>.writes(
    ghost: VarDecl<ArrayType<*, *>>,
    ghosts: Map<VarDecl<ArrayType<*, *>>, Expr<*>>,
  ): List<Stmt> =
    when {
      this == ghost.ref -> listOf()
      this is ArrayLitExpr<*, *> -> {
        check(elseElem == ghost.type.elemType.defaultValue) { "Unsupported value of $ghost: $this" }
        elements.map { entry ->
          MemoryAssignStmt.of(
            cell(ghost, ghosts, entry.get1()),
            cast(entry.get2(), ghost.type.elemType) as Expr<Type>,
          )
        }
      }
      this is ArrayWriteExpr<*, *> ->
        array.writes(ghost, ghosts) +
          MemoryAssignStmt.of(
            cell(ghost, ghosts, index.rewrite(ghosts)),
            cast(elem.rewrite(ghosts), ghost.type.elemType) as Expr<Type>,
          )
      else -> error("Unsupported value of $ghost: $this")
    }

  private fun Expr<*>.rewrite(ghosts: Map<VarDecl<ArrayType<*, *>>, Expr<*>>): Expr<*> {
    if (this is ArrayReadExpr<*, *>) {
      (array as? ArrayLitExpr<*, *>)?.let { literal ->
        val at = index.rewrite(ghosts)
        return literal.elements.fold(literal.elseElem as Expr<*>) { rest, entry ->
          Ite<Type>(Eq(at, entry.get1()), entry.get2(), rest)
        }
      }
      val ghost = ghosts.keys.find { it.ref == array } ?: error("Unsupported array read: $this")
      val at = index.rewrite(ghosts)
      val rest: Expr<*> =
        if (ghost in census.dynamicWrites) cell(ghost, ghosts, at)
        else ghost.type.elemType.defaultValue
      return census.tables.getValue(ghost).entries.fold(rest) { other, (key, value) ->
        Ite<Type>(Eq(at, key), value, other)
      }
    }
    check(type !is ArrayType<*, *>) { "Unsupported array term: $this" }
    return if (ops.isEmpty()) this else map { it.rewrite(ghosts) }
  }

  @Suppress("UNCHECKED_CAST")
  private fun cell(
    ghost: VarDecl<ArrayType<*, *>>,
    ghosts: Map<VarDecl<ArrayType<*, *>>, Expr<*>>,
    index: Expr<*>,
  ): Dereference<Type, Type, Type> =
    Dereference.of(
      ghosts.getValue(ghost) as Expr<Type>,
      index as Expr<Type>,
      ghost.type.elemType as Type,
    )
}
