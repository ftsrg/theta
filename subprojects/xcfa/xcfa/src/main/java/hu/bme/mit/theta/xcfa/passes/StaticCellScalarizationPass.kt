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
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Ite
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.MemoryCell
import hu.bme.mit.theta.xcfa.utils.MemoryTypeKey
import hu.bme.mit.theta.xcfa.utils.ValueSetAnalysis
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.memoryTypeKey
import hu.bme.mit.theta.xcfa.utils.toLitOrNull

/**
 * Turns memory cells into variables. A partition is scalarized only if the [ValueSetAnalysis]
 * bounds all its accesses to at most [MAX_CELLS] candidate cells; an access then becomes its single
 * cell variable, or a case split over its candidate cells. Other partitions are left to
 * [DereferenceToArrayPass].
 *
 * [round] only keeps the variable names unique when the pass runs again (see
 * [StateReductionPasses]).
 */
class StaticCellScalarizationPass(private val round: Int = 0) : ProcedurePass {

  companion object {
    private const val MAX_CELLS = 256
  }

  /** The variables of a scalarized partition; [caseSplit] is null if every access hits one cell. */
  private class Partition(val cellVars: Map<MemoryCell, VarDecl<*>>, val caseSplit: CaseSplitVars?)

  /**
   * The helpers of accesses with several candidate cells. [unknownReads] give the reads that hit no
   * candidate, one per such read in a statement; [base], [offset] and [writtenValue] save a write.
   */
  private class CaseSplitVars(
    val unknownReads: MutableList<VarDecl<*>>,
    val base: VarDecl<*>,
    val offset: VarDecl<*>,
    val writtenValue: VarDecl<*>,
  )

  private lateinit var analysis: ValueSetAnalysis
  private lateinit var partitions: Map<MemoryTypeKey, Partition>
  private var nextId = 0

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    // A whole-program pass: the first call analyzes and rewrites every procedure.
    if (!::partitions.isInitialized) {
      val xcfa = builder.parent
      analysis = ValueSetAnalysis(xcfa, DereferenceToArrayPass.zeroInitialized)
      partitions = scalarizablePartitions(xcfa)
      if (partitions.isNotEmpty()) xcfa.getProcedures().forEach { rewrite(it) }
      val newVars =
        partitions.values.flatMap { p ->
          p.cellVars.values +
            listOfNotNull(p.caseSplit).flatMap {
              it.unknownReads + it.base + it.offset + it.writtenValue
            }
        }
      xcfa.addMemoryGlobals(newVars.map { it to it.type.defaultValue })
    }
    return builder
  }

  private fun scalarizablePartitions(xcfa: XcfaBuilder): Map<MemoryTypeKey, Partition> {
    val labels = xcfa.getProcedures().flatMap { p -> p.getEdges().flatMap { it.getFlatLabels() } }
    // Only these statements are rewritten; partitions also accessed elsewhere stay in memory.
    val accessedElsewhere =
      labels
        .filterNot { it.isRewritable() }
        .flatMap { it.dereferences }
        .map { it.memoryTypeKey }
        .toSet()
    return labels
      .flatMap { it.dereferences }
      .groupBy { it.memoryTypeKey }
      .filterKeys { it !in accessedElsewhere }
      .mapNotNull { (key, derefs) -> partitionOf(key, derefs)?.let { key to it } }
      .toMap()
  }

  private fun partitionOf(key: MemoryTypeKey, derefs: List<Dereference<*, *, *>>): Partition? {
    val cells = derefs.flatMap { it.candidateCells() ?: return null }.toSet()
    if (cells.size > MAX_CELLS) return null
    val cellVars = cells.associateWith { freshVar("", key.elemType) }
    val caseSplit =
      if (derefs.all { it.literalCell() != null }) null
      else
        CaseSplitVars(
          mutableListOf(),
          freshVar("base_", key.arrayType),
          freshVar("offset_", key.offsetType),
          freshVar("value_", key.elemType),
        )
    return Partition(cellVars, caseSplit)
  }

  private fun XcfaLabel.isRewritable(): Boolean =
    this is StmtLabel &&
      (stmt is AssignStmt<*> || stmt is MemoryAssignStmt<*, *, *> || stmt is AssumeStmt)

  /**
   * The cells [this] may reach, or null if they are unbounded. Base 0 is an ordinary row, as in
   * [DereferenceToArrayPass]: the flat memory model puts all memory there.
   */
  private fun Dereference<*, *, *>.candidateCells(): List<MemoryCell>? = analysis.cells(this)

  /** The cell of a dereference with a literal address, or null. */
  private fun Dereference<*, *, *>.literalCell(): MemoryCell? {
    val base = array.toLitOrNull() ?: return null
    val offset = offset.toLitOrNull() ?: return null
    return MemoryCell(memoryTypeKey, base, offset)
  }

  private fun freshVar(kind: String, type: Type): VarDecl<*> =
    Decls.Var("__cell${round}_$kind${nextId++}", type)

  private fun Partition.singleCellVar(d: Dereference<*, *, *>): VarDecl<*>? =
    d.literalCell()?.let { cellVars.getValue(it) }

  /**
   * The candidate cells of [d], each with the condition that the address [base], [offset] hits it.
   */
  private fun Partition.guardedCells(
    d: Dereference<*, *, *>,
    base: Expr<*>,
    offset: Expr<*>,
  ): List<Pair<VarDecl<*>, Expr<BoolType>>> {
    val literalBase = d.array.toLitOrNull() != null
    val literalOffset = d.offset.toLitOrNull() != null
    return d.candidateCells()!!.map { c ->
      val guard =
        listOfNotNull(
          if (literalBase) null else Eq(base, c.base),
          if (literalOffset) null else Eq(offset, c.offset),
        )
      cellVars.getValue(c) to And(guard)
    }
  }

  private fun rewrite(builder: XcfaProcedureBuilder) {
    builder.getEdges().toList().forEach { edge ->
      val newLabel = edge.label.scalarize()
      if (newLabel != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
  }

  private fun XcfaLabel.scalarize(): XcfaLabel =
    when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.scalarize() }, metadata)
      is StmtLabel -> scalarize()
      else -> this // accesses no scalarized partition, see accessedElsewhere
    }

  private fun StmtLabel.scalarize(): XcfaLabel {
    val unknownReads = mutableListOf<VarDecl<*>>()
    val stmts =
      when (stmt) {
        is MemoryAssignStmt<*, *, *> -> stmt.scalarize(unknownReads)
        is AssignStmt<*> -> listOf(assign(stmt.varDecl, stmt.expr.scalarize(unknownReads)))
        is AssumeStmt -> listOf(AssumeStmt.of(stmt.cond.scalarize(unknownReads)))
        else -> listOf(stmt)
      }
    // Havoced before and reset after, so the unknown reads add no state between statements.
    val all = unknownReads.map { HavocStmt.of(it) } + stmts + unknownReads.map(::resetToDefault)
    if (all == listOf(stmt)) return this
    if (all.size == 1) return StmtLabel(all[0], choiceType, metadata)
    return SequenceLabel(all.map { StmtLabel(it, choiceType, metadata) }, metadata)
  }

  private fun MemoryAssignStmt<*, *, *>.scalarize(
    unknownReads: MutableList<VarDecl<*>>
  ): List<Stmt> {
    val value = expr.scalarize(unknownReads)
    val partition = partitions[deref.memoryTypeKey]
    if (partition == null) {
      val address = deref.scalarize(unknownReads) as Dereference<*, *, *>
      return listOf(MemoryAssignStmt.create(address, value))
    }
    partition.singleCellVar(deref)?.let {
      return listOf(assign(it, value))
    }
    val split = partition.caseSplit!!
    // Saved first: the address and the value may read a candidate cell that is updated below.
    val save =
      listOf(
        assign(split.base, deref.array.scalarize(unknownReads)),
        assign(split.offset, deref.offset.scalarize(unknownReads)),
        assign(split.writtenValue, value),
      )
    val update =
      partition.guardedCells(deref, split.base.ref, split.offset.ref).map { (v, guard) ->
        assign(v, Ite(guard, cast(split.writtenValue.ref, v.type), cast(v.ref, v.type)))
      }
    return save +
      update +
      listOf(split.base, split.offset, split.writtenValue).map(::resetToDefault)
  }

  private fun <T : Type> Expr<T>.scalarize(unknownReads: MutableList<VarDecl<*>>): Expr<T> {
    val d = this as? Dereference<*, *, *>
    val partition = d?.let { partitions[it.memoryTypeKey] }
    if (d == null || partition == null) return withOps(ops.map { it.scalarize(unknownReads) })
    partition.singleCellVar(d)?.let {
      return cast(it.ref, type)
    }
    val split = partition.caseSplit!!
    val unknownRead = split.unknownReadFor(unknownReads)
    val base = d.array.scalarize(unknownReads)
    val offset = d.offset.scalarize(unknownReads)
    // A read that hits no candidate cell gives any value: its address is read only in assumptions,
    // whose values ValueSetAnalysis does not track.
    val read =
      partition.guardedCells(d, base, offset).foldRight<_, Expr<*>>(unknownRead.ref) {
        (v, guard),
        rest ->
        Ite(guard, cast(v.ref, type), cast(rest, type))
      }
    return cast(read, type)
  }

  /**
   * An unknown-read helper not yet used in the statement, so that two such reads are independent.
   */
  private fun CaseSplitVars.unknownReadFor(usedInStmt: MutableList<VarDecl<*>>): VarDecl<*> {
    val index = usedInStmt.count { it in unknownReads }
    if (index == unknownReads.size) unknownReads += freshVar("unknown_", writtenValue.type)
    return unknownReads[index].also { usedInStmt += it }
  }

  private fun assign(v: VarDecl<*>, e: Expr<*>): Stmt =
    AssignStmt.of(cast(v, v.type), cast(e, v.type))

  private fun resetToDefault(v: VarDecl<*>): Stmt = assign(v, v.type.defaultValue)
}
