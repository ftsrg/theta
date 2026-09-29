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

import com.google.common.collect.Sets
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isRead
import java.math.BigInteger
import java.util.Collections
import java.util.IdentityHashMap

/**
 * Remove unused variables from the program. Requires the ProcedureBuilder to be `deterministic`
 * (@see DeterministicPass)
 *
 * Given a [ParseContext], unread writes to global objects are removed as well (see
 * [UnusedMemoryWriteRemoval]).
 */
class UnusedVarPass(
  private val uniqueWarningLogger: Logger,
  val property: XcfaProperty? = null,
  parseContext: ParseContext? = null,
) : ProcedurePass {

  private val memoryWriteRemoval = parseContext?.let(::UnusedMemoryWriteRemoval)

  companion object {
    var keepGlobalVariableAccesses = false
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val isOverflow = property?.verifiedProperty?.equals(ErrorDetection.OVERFLOW) ?: false
    checkNotNull(builder.metaData["deterministic"])

    val usedVars = LinkedHashSet<VarDecl<*>>()
    val globalVars = builder.parent.getVars().map { it.wrappedVar }.toSet()

    var edges = LinkedHashSet(builder.parent.getProcedures().flatMap { it.getEdges() })
    lateinit var lastEdges: Set<XcfaEdge>
    do {
      lastEdges = edges

      usedVars.clear()

      if (keepGlobalVariableAccesses) {
        usedVars.addAll(globalVars)
      }

      usedVars.addAll(
        builder.parent.getProcedures().flatMap {
          it.getParams().filter { it.second != ParamDirection.IN }.map { it.first }
        }
      )
      edges.forEach { edge ->
        usedVars.addAll(
          edge.label.collectVarsWithAccessType().filter { it.value.isRead }.map { it.key }
        )
        if (isOverflow) {
          for (label in edge.getFlatLabels()) {
            if (label is StmtLabel && label.stmt is AssignStmt<*> && label.stmt.expr !is RefExpr) {
              usedVars.add(label.stmt.varDecl)
            }
          }
        }
      }

      builder.parent.getProcedures().forEach { b ->
        b.getEdges().toList().forEach { edge ->
          val newLabel = edge.label.removeUnusedWrites(usedVars, globalVars)
          if (newLabel != edge.label) {
            b.removeEdge(edge)
            b.addEdge(edge.withLabel(newLabel))
          }
        }
      }
      if (!keepGlobalVariableAccesses && !isOverflow) {
        memoryWriteRemoval?.run(builder.parent.getProcedures())
      }

      edges = LinkedHashSet(builder.parent.getProcedures().flatMap { it.getEdges() })
    } while (lastEdges != edges)

    val allVars =
      Sets.union(
        builder.parent.getProcedures().flatMap { it.getVars() }.toSet(),
        builder.parent.getVars().map { it.wrappedVar }.toSet(),
      )
    val varsAndParams = Sets.union(allVars, builder.getParams().map { it.first }.toSet())
    if (!varsAndParams.containsAll(usedVars)) {
      uniqueWarningLogger.writeln(
        Logger.Level.INFO,
        "WARNING: There are some used variables not present as declarations: " +
          usedVars.filter { it !in varsAndParams },
      )
    }

    builder.getVars().filter { it !in usedVars }.forEach { builder.removeVar(it) }

    return builder
  }

  private fun XcfaLabel.removeUnusedWrites(
    used: Set<VarDecl<*>>,
    global: Set<VarDecl<*>>,
  ): XcfaLabel {
    return when (this) {
      is SequenceLabel ->
        SequenceLabel(labels.map { it.removeUnusedWrites(used, global) }.filter { it !is NopLabel })

      is NondetLabel ->
        NondetLabel(
          labels.map { it.removeUnusedWrites(used, global) }.filter { it !is NopLabel }.toSet()
        )

      is StmtLabel ->
        when (stmt) {
          is AssignStmt<*> ->
            if (
              stmt.varDecl in used ||
                (keepGlobalVariableAccesses &&
                  (ExprUtils.getVars(stmt.expr).any { it in global } ||
                    stmt.expr.dereferences.isNotEmpty()))
            )
              this
            else NopLabel
          is HavocStmt<*> -> if (stmt.varDecl in used) this else NopLabel
          else -> this
        }

      else -> this
    }
  }
}

/**
 * Removes the writes to global objects (see [ParseContext.isStaticObject]) that no read may reach.
 * A union is only removed as a whole: a read of any part of it keeps every write to it.
 *
 * Within an edge, a value written to a cell is forwarded into the addresses that read that cell
 * back, so the members of nested objects resolve to the object they belong to.
 */
private class UnusedMemoryWriteRemoval(private val parseContext: ParseContext) {

  private data class Lit(val type: Type, val value: BigInteger)

  /** A memory cell, where null stands for an unknown part of its address. */
  private data class Cell(val base: Lit?, val offset: Lit?)

  private class Write(
    val label: StmtLabel,
    val cell: Cell,
    val removable: Boolean,
    val union: BigInteger?,
  )

  private class Offsets {
    private var unknown = false
    private val literals = HashSet<Lit>()
    private val types = HashSet<Type>()

    fun add(offset: Lit?) {
      if (offset == null) {
        unknown = true
      } else {
        literals.add(offset)
        types.add(offset.type)
      }
    }

    fun mayContain(offset: Lit?): Boolean =
      unknown || offset == null || offset in literals || types.any { it != offset.type }
  }

  private val flat = parseContext.memoryModel.flatAddressing()
  private val reads = HashMap<Lit?, Offsets>()
  private val readObjects = HashSet<BigInteger>()
  private val writes = ArrayList<Write>()

  fun run(procedures: Collection<XcfaProcedureBuilder>) {
    reads.clear()
    readObjects.clear()
    writes.clear()
    val names = procedures.map { it.name }.toSet()
    val labels =
      procedures.associateWith { procedure ->
        procedure.getEdges().associateWith { it.label.forward(KnownCells()) }
      }
    if (!labels.values.all { edges -> edges.values.all { it.collect(names, true) } }) return

    val usedUnions = readObjects.mapNotNullTo(HashSet(), parseContext::enclosingStaticUnion)
    writes.forEach { if (it.union != null && mayBeRead(it.cell)) usedUnions.add(it.union) }
    val unused = identitySet()
    val used = identitySet()
    writes.forEach {
      val isUnused =
        it.removable && if (it.union != null) it.union !in usedUnions else !mayBeRead(it.cell)
      (if (isUnused) unused else used).add(it.label)
    }
    unused.removeAll(used)

    labels.forEach { (procedure, edges) ->
      edges.forEach { (edge, label) ->
        val newLabel = label.without(unused)
        if (newLabel != edge.label) {
          procedure.removeEdge(edge)
          procedure.addEdge(edge.withLabel(newLabel))
        }
      }
    }
  }

  private fun identitySet(): MutableSet<XcfaLabel> =
    Collections.newSetFromMap(IdentityHashMap<XcfaLabel, Boolean>())

  private fun mayEqual(a: Lit?, b: Lit?): Boolean =
    a == null || b == null || a.type != b.type || a.value == b.value

  private fun mayAlias(a: Cell, b: Cell): Boolean =
    mayEqual(a.base, b.base) && mayEqual(a.offset, b.offset)

  private fun mayBeRead(cell: Cell): Boolean =
    reads.any { (base, offsets) -> mayEqual(base, cell.base) && offsets.mayContain(cell.offset) }

  private fun literalOf(expr: Expr<*>): Lit? {
    val simplified = if (expr is LitExpr<*>) expr else ExprUtils.simplify(expr)
    return simplified.asConstantBigInteger()?.let { literalOf(simplified.type, it) }
  }

  private fun literalOf(type: Type, value: BigInteger): Lit =
    Lit(type, if (type is BvType) value.mod(BigInteger.TWO.pow(type.size)) else value)

  /** Under flat addressing, the cell is identified by its address alone. */
  private fun cellOf(deref: Dereference<*, *, *>): Cell {
    val base = literalOf(deref.array)
    val offset = literalOf(deref.offset)
    if (!flat) return Cell(base, offset)
    val address =
      if (base == null || offset == null || base.type != offset.type) null
      else literalOf(offset.type, base.value + offset.value)
    return Cell(null, address)
  }

  private val Cell.isKnown: Boolean
    get() = offset != null && (flat || base != null)

  private fun objectOf(cell: Cell): BigInteger? =
    if (flat) cell.offset?.value?.divide(BigInteger.valueOf(FlatMemoryPass.FLAT_STRIDE))
    else cell.base?.value

  /** The values of the cells written earlier in the edge. */
  private inner class KnownCells(
    val values: HashMap<Cell, LitExpr<*>> = HashMap(),
    private val types: HashSet<Pair<Type?, Type?>> = HashSet(),
  ) {
    fun copy() = KnownCells(HashMap(values), HashSet(types))

    fun clear() {
      values.clear()
      types.clear()
    }

    fun write(cell: Cell, value: Expr<*>) {
      val cellTypes = cell.base?.type to cell.offset?.type
      if (cell.isKnown && types.all { it == cellTypes }) values.remove(cell)
      else values.keys.removeIf { mayAlias(it, cell) }
      if (value is LitExpr<*> && cell.isKnown) {
        values[cell] = value
        types.add(cellTypes)
      }
    }
  }

  private fun XcfaLabel.forward(known: KnownCells): XcfaLabel =
    when (this) {
      is SequenceLabel ->
        labels.map { it.forward(known) }.let { if (it.sameAs(labels)) this else copy(labels = it) }
      is NondetLabel -> {
        val branches = labels.toList()
        val forwarded = branches.map { it.forward(known.copy()) }
        known.clear()
        if (forwarded.sameAs(branches)) this else copy(labels = forwarded.toSet())
      }
      is StmtLabel -> forward(known)
      is NopLabel -> this
      else -> this.also { known.clear() }
    }

  private fun StmtLabel.forward(known: KnownCells): StmtLabel {
    val newStmt =
      when (stmt) {
        is MemoryAssignStmt<*, *, *> -> {
          val deref = stmt.deref.forwardAddress(known.values)
          val expr = stmt.expr.forwardAddresses(known.values)
          known.write(cellOf(deref), expr)
          if (deref === stmt.deref && expr === stmt.expr) stmt else memoryAssign(deref, expr)
        }
        is AssignStmt<*> ->
          stmt.expr.forwardAddresses(known.values).let {
            if (it === stmt.expr) stmt else AssignStmt.create<Type>(stmt.varDecl, it)
          }
        is AssumeStmt ->
          stmt.cond.forwardAddresses(known.values).let {
            if (it === stmt.cond) stmt else AssumeStmt.create(it)
          }
        else -> stmt
      }
    return if (newStmt === stmt) this else copy(stmt = newStmt)
  }

  private fun <P : Type, O : Type, D : Type> memoryAssign(
    deref: Dereference<P, O, D>,
    expr: Expr<*>,
  ): MemoryAssignStmt<P, O, D> = MemoryAssignStmt.create(deref, cast(expr, deref.type))

  /** Forwards the addresses of the dereferences in this expression. */
  private fun Expr<*>.forwardAddresses(known: Map<Cell, LitExpr<*>>): Expr<*> =
    if (this is Dereference<*, *, *>) forwardAddress(known)
    else ops.map { it.forwardAddresses(known) }.let { if (it.sameAs(ops)) this else withOps(it) }

  @Suppress("UNCHECKED_CAST")
  private fun <P : Type, O : Type, D : Type> Dereference<P, O, D>.forwardAddress(
    known: Map<Cell, LitExpr<*>>
  ): Dereference<P, O, D> {
    val newArray = array.resolve(known)
    val newOffset = offset.resolve(known)
    return if (newArray === array && newOffset === offset) this
    else withOps(listOf(newArray, newOffset) + ops.drop(2)) as Dereference<P, O, D>
  }

  /** Replaces the dereferences of known cells in this address by the value they hold. */
  private fun Expr<*>.resolve(known: Map<Cell, LitExpr<*>>): Expr<*> {
    val resolved =
      if (this is Dereference<*, *, *>) {
        val deref = forwardAddress(known)
        known.takeIf { it.isNotEmpty() }?.get(cellOf(deref))?.takeIf { it.type == type } ?: deref
      } else {
        ops.map { it.resolve(known) }.let { if (it.sameAs(ops)) this else withOps(it) }
      }
    return if (resolved === this) this else ExprUtils.simplify(resolved)
  }

  private fun XcfaLabel.collect(procedures: Set<String>, removable: Boolean): Boolean =
    when (this) {
      is SequenceLabel -> labels.all { it.collect(procedures, true) }
      is NondetLabel -> labels.all { it.collect(procedures, false) }
      is StmtLabel ->
        when (stmt) {
          is MemoryAssignStmt<*, *, *> -> {
            stmt.deref.ops.forEach(::addReads)
            addReads(stmt.expr)
            val cell = cellOf(stmt.deref)
            val obj = objectOf(cell)?.takeIf(parseContext::isStaticObject)
            val union = obj?.let(parseContext::enclosingStaticUnion)
            writes.add(Write(this, cell, removable && obj != null, union))
            true
          }
          is AssignStmt<*> -> {
            addReads(stmt.expr)
            true
          }
          is AssumeStmt -> {
            addReads(stmt.cond)
            true
          }
          is HavocStmt<*>,
          is SkipStmt -> true
          else -> false
        }
      // a callee outside the XCFA may access memory in ways no label shows
      is InvokeLabel -> (name in procedures).also { params.forEach(::addReads) }
      is StartLabel -> (name in procedures).also { params.forEach(::addReads) }
      is FenceLabel -> {
        addReads(lock)
        true
      }
      is ReturnLabel -> enclosedLabel.collect(procedures, false)
      is JoinLabel,
      is NopLabel -> true
    }

  private fun addReads(expr: Expr<*>) {
    if (expr is Dereference<*, *, *>) {
      val cell = cellOf(expr)
      reads.getOrPut(cell.base) { Offsets() }.add(cell.offset)
      objectOf(cell)?.let(readObjects::add)
    }
    expr.ops.forEach(::addReads)
  }

  private fun XcfaLabel.without(unused: Set<XcfaLabel>): XcfaLabel =
    when (this) {
      is SequenceLabel ->
        labels
          .filter { it !in unused }
          .map { it.without(unused) }
          .let { if (it.sameAs(labels)) this else copy(labels = it) }
      is NondetLabel -> {
        val branches = labels.toList()
        val kept = branches.map { it.without(unused) }
        if (kept.sameAs(branches)) this else copy(labels = kept.toSet())
      }
      else -> this
    }

  private fun List<*>.sameAs(other: List<*>): Boolean =
    size == other.size && indices.all { this[it] === other[it] }
}
