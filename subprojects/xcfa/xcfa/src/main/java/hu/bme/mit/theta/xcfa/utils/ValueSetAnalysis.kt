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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import java.math.BigInteger

data class MemoryCell(val key: MemoryTypeKey, val base: LitExpr<*>, val offset: LitExpr<*>)

// null is top
typealias ValueSet = Set<LitExpr<*>>?

internal fun Expr<*>.toLitOrNull(): LitExpr<*>? = ExprUtils.simplify(this) as? LitExpr<*>

/** Flow-insensitive value-set analysis, so the result covers every thread interleaving. */
class ValueSetAnalysis(
  xcfa: XcfaBuilder,
  private val zeroInitialized: Boolean,
  private val maxValues: Int = 64,
) {

  private sealed interface Write

  private class VarWrite(val varDecl: VarDecl<*>, val value: Expr<*>) : Write

  private class MemoryWrite(val deref: Dereference<*, *, *>, val value: Expr<*>) : Write

  private val varValues = mutableMapOf<VarDecl<*>, ValueSet>()
  private val cellValues = mutableMapOf<MemoryCell, ValueSet>()
  private val topPartitions = mutableSetOf<MemoryTypeKey>()

  init {
    val labels = xcfa.getProcedures().flatMap { p -> p.getEdges().flatMap { it.getAllLabels() } }
    val (writes, topVars) = collectWrites(xcfa, labels)
    val startWrites = startArgumentWrites(xcfa, labels)
    val allWrites = writes + startWrites
    val assigned = allWrites.filterIsInstance<VarWrite>().map { it.varDecl }.toSet() - topVars
    seedStartValues(xcfa, assigned, startWrites.map { it.varDecl }.toSet())
    do {
      var changed = false
      for (w in allWrites) changed = apply(w) || changed
    } while (changed)
  }

  fun values(e: Expr<*>): ValueSet {
    e.toLitOrNull()?.let {
      return setOf(it)
    }
    return when (e) {
      is RefExpr<*> -> varValues[e.decl]
      is Dereference<*, *, *> ->
        cells(e)?.fold<MemoryCell, ValueSet>(emptySet()) { acc, c -> join(acc, valueOf(c)) }
      else -> remainderRange(e) ?: combinations(e)
    }
  }

  fun cells(d: Dereference<*, *, *>): List<MemoryCell>? {
    if (d.memoryTypeKey in topPartitions) return null
    val bases = values(d.array) ?: return null
    val offsets = values(d.offset) ?: return null
    return bases.flatMap { b -> offsets.map { o -> MemoryCell(d.memoryTypeKey, b, o) } }
  }

  private fun valueOf(c: MemoryCell): ValueSet =
    when {
      c in cellValues -> cellValues[c]
      zeroInitialized -> setOf(c.key.elemType.defaultValue)
      else -> null
    }

  private fun join(a: ValueSet, b: ValueSet): ValueSet =
    if (a == null || b == null) null else (a + b).takeIf { it.size <= maxValues }

  private fun remainderRange(e: Expr<*>): Set<LitExpr<*>>? {
    if (e !is BvURemExpr && e !is IntModExpr) return null
    val (size, literal) =
      when (val n = e.ops[1].toLitOrNull()) {
        is BvLitExpr ->
          BvUtils.neutralBvLitExprToBigInteger(n) to { k: Int -> bvLiteral(k, n.type) }
        is IntLitExpr -> n.value to { k: Int -> Int(k) }
        else -> return null
      }
    if (size.signum() <= 0 || size > BigInteger.valueOf(maxValues.toLong())) return null
    return (0 until size.toInt()).map(literal).toSet()
  }

  private fun bvLiteral(k: Int, type: BvType): LitExpr<*> =
    BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(k.toLong()), type.size).let {
      if (type.signedness != null) Bv(it.value, type.signedness) else it
    }

  private fun combinations(e: Expr<*>): ValueSet {
    val atoms = linkedSetOf<Expr<*>>()
    fun collect(x: Expr<*>) {
      when {
        x.toLitOrNull() != null -> {}
        x is RefExpr<*> || x is Dereference<*, *, *> -> atoms.add(x)
        else -> x.ops.forEach(::collect)
      }
    }
    collect(e)
    val atomValues = atoms.map { values(it)?.toList() ?: return null }
    if (atomValues.fold(1L) { acc, l -> minOf(acc * l.size, maxValues + 1L) } > maxValues)
      return null
    var valuations = listOf(emptyMap<Expr<*>, Expr<*>>())
    atoms.zip(atomValues).forEach { (atom, vs) ->
      valuations = valuations.flatMap { l -> vs.map { l + (atom to it) } }
    }
    return valuations.map { ExprUtils.changeSubexpr(e, it).toLitOrNull() ?: return null }.toSet()
  }

  private fun <K> MutableMap<K, ValueSet>.update(key: K, old: ValueSet, value: ValueSet): Boolean {
    val new = join(old, value)
    this[key] = new
    return new != old
  }

  private fun apply(w: Write): Boolean =
    when (w) {
      is VarWrite -> varValues.update(w.varDecl, varValues[w.varDecl], values(w.value))
      is MemoryWrite -> {
        val cells = cells(w.deref)
        if (cells == null) topPartitions.add(w.deref.memoryTypeKey)
        else {
          val value = values(w.value)
          cells.fold(false) { changed, c -> cellValues.update(c, valueOf(c), value) || changed }
        }
      }
    }

  private fun collectWrites(
    xcfa: XcfaBuilder,
    labels: List<XcfaLabel>,
  ): Pair<List<Write>, Set<VarDecl<*>>> {
    val writes = mutableListOf<Write>()
    val topVars = mutableSetOf<VarDecl<*>>()
    for (label in labels) {
      when (val stmt = (label as? StmtLabel)?.stmt) {
        is AssignStmt<*> -> writes += VarWrite(stmt.varDecl, stmt.expr)
        is MemoryAssignStmt<*, *, *> -> writes += MemoryWrite(stmt.deref, stmt.expr)
        is AssumeStmt -> {}
        else -> {
          topVars += label.collectVarsWithAccessType().filter { it.value.isWritten }.keys
          if (label is InvokeLabel) topVars += outArguments(xcfa, label)
          topPartitions +=
            label.dereferencesWithAccessType
              .filter { it.value.isWritten }
              .keys
              .map { it.memoryTypeKey }
        }
      }
    }
    return writes to topVars
  }

  private fun outArguments(xcfa: XcfaBuilder, call: InvokeLabel): List<VarDecl<*>> {
    val params = xcfa.getProcedures().find { it.name == call.name }?.getParams()
    return call.params
      .filterIndexed { i, _ -> params?.getOrNull(i)?.second != ParamDirection.IN }
      .flatMap { ExprUtils.getVars(it) }
  }

  private fun startArgumentWrites(xcfa: XcfaBuilder, labels: List<XcfaLabel>): List<VarWrite> =
    labels.filterIsInstance<StartLabel>().flatMap { start ->
      val proc = xcfa.getProcedures().find { it.name == start.name } ?: return@flatMap emptyList()
      proc
        .getParams()
        .zip(start.params)
        .filter { (param, _) -> param.second != ParamDirection.OUT }
        .map { (param, arg) -> VarWrite(param.first, arg) }
    }

  private fun seedStartValues(
    xcfa: XcfaBuilder,
    assigned: Set<VarDecl<*>>,
    startParams: Set<VarDecl<*>>,
  ) {
    val globals = xcfa.getVars().associateBy { it.wrappedVar }
    val readBeforeWritten =
      xcfa.getProcedures().flatMap { readBeforeWritten(it) }.toSet() - startParams
    for (v in assigned) {
      varValues[v] =
        when {
          v in globals ->
            globals[v]!!.initValue?.let { setOf(it) }
              ?: if (zeroInitialized) setOf(v.type.defaultValue) else null
          v in readBeforeWritten -> null
          else -> emptySet()
        }
    }
  }

  private fun readBeforeWritten(p: XcfaProcedureBuilder): Set<VarDecl<*>> {
    fun step(label: XcfaLabel, liveOut: Set<VarDecl<*>>): Set<VarDecl<*>> =
      when (label) {
        is SequenceLabel -> label.labels.foldRight(liveOut) { l, acc -> step(l, acc) }
        is NondetLabel -> label.labels.flatMap { step(it, liveOut) }.toSet()
        is StmtLabel ->
          when (val stmt = label.stmt) {
            is AssumeStmt -> liveOut
            is AssignStmt<*> -> liveOut - stmt.varDecl + ExprUtils.getVars(stmt.expr)
            is HavocStmt<*> -> liveOut - stmt.varDecl
            else -> liveOut + label.collectVarsWithAccessType().keys
          }
        else -> liveOut + label.collectVarsWithAccessType().keys
      }
    val live = mutableMapOf<XcfaLocation, Set<VarDecl<*>>>()
    val worklist = ArrayDeque(p.getLocs())
    while (worklist.isNotEmpty()) {
      val loc = worklist.removeFirst()
      val out = loc.outgoingEdges.flatMap { step(it.label, live[it.target] ?: emptySet()) }.toSet()
      if (out != (live[loc] ?: emptySet<VarDecl<*>>())) {
        live[loc] = out
        loc.incomingEdges.forEach { if (it.source !in worklist) worklist.addLast(it.source) }
      }
    }
    return live[p.initLoc] ?: emptySet()
  }
}
