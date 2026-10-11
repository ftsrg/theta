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
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Ite
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.MemoryTypeKey
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import hu.bme.mit.theta.xcfa.utils.memoryTypeKey

/**
 * Turns memory cells into variables, so that a decision-diagram backend sees small scalar domains
 * instead of one array-valued variable per memory partition.
 *
 * A flow-insensitive value analysis bounds the bases and offsets each access may use. A partition
 * is split only if every access has a bounded set of bases and of offsets: each reachable cell then
 * gets a variable, an access with a single constant cell uses it directly, and any other access
 * becomes a case split over its candidate cells. The pass runs on all procedures at once; [round]
 * keeps the names of a later run apart. A cell no access reads becomes a variable [UnusedVarPass]
 * removes.
 */
class StaticCellScalarizationPass(private val round: Int = 0) : ProcedurePass {

  private data class Cell(val key: MemoryTypeKey, val base: LitExpr<*>, val offset: LitExpr<*>)

  /** Per-partition helper variables for variable-offset accesses. */
  private class Helpers(
    val unknown: VarDecl<*>,
    val base: VarDecl<*>,
    val offset: VarDecl<*>,
    val value: VarDecl<*>,
  )

  private var cells: MutableMap<Cell, VarDecl<*>>? = null
  private val cellsOfBase = mutableMapOf<Pair<MemoryTypeKey, LitExpr<*>>, MutableList<Cell>>()
  private val helpers = mutableMapOf<MemoryTypeKey, Helpers>()
  private val eligible = mutableSetOf<MemoryTypeKey>()

  private fun Expr<*>.lit(): LitExpr<*>? =
    try {
      eval(ImmutableValuation.empty())
    } catch (e: Exception) {
      null
    }

  private fun Dereference<*, *, *>.cell(): Cell? {
    val base = array.lit() ?: return null
    val off = offset.lit() ?: return null
    return Cell(memoryTypeKey, base, off)
  }

  private fun XcfaBuilder.addGlobal(v: VarDecl<*>): StmtLabel {
    val (global, initLabel) =
      if (DereferenceToArrayPass.zeroInitialized) {
        XcfaGlobalVar(v, v.type.defaultValue, atomic = true) to
          StmtLabel(AssignStmt.of(cast(v, v.type), cast(v.type.defaultValue, v.type)))
      } else {
        XcfaGlobalVar(v, atomic = true) to StmtLabel(HavocStmt.of(v))
      }
    addVar(global)
    return initLabel
  }

  // ---- value sets: the literals a variable or a constant cell can hold (null: unknown) ----
  private val maxValues = 64
  private val maxCells = 256
  private val varValues = mutableMapOf<VarDecl<*>, MutableSet<LitExpr<*>>?>()
  private val cellValues = mutableMapOf<Cell, MutableSet<LitExpr<*>>?>()

  private fun union(a: Set<LitExpr<*>>?, b: Set<LitExpr<*>>?): MutableSet<LitExpr<*>>? =
    if (a == null || b == null) null else (a + b).toMutableSet().takeIf { it.size <= maxValues }

  /** Literals [e] can evaluate to, from the current sets of the variables and cells it reads. */
  private fun values(e: Expr<*>, depth: Int = 0): Set<LitExpr<*>>? {
    e.lit()?.let {
      return setOf(it)
    }
    if (depth > 30) return null
    when (e) {
      is RefExpr<*> -> return if (e.decl in varValues) varValues[e.decl] else null
      is Dereference<*, *, *> -> {
        val bases = values(e.array, depth + 1) ?: return null
        val offs = values(e.offset, depth + 1) ?: return null
        var acc: MutableSet<LitExpr<*>>? = mutableSetOf()
        for (b in bases) for (o in offs) acc =
          union(acc, cellValues[Cell(e.memoryTypeKey, b, o)] ?: return null)
        return acc
      }
    }
    // x % c with a literal c lies in [0, c) whatever x is
    if (e is BvURemExpr || e is IntModExpr) {
      val c = e.ops[1].lit()
      val n =
        when (c) {
          is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(c)
          is IntLitExpr -> c.value
          else -> null
        }
      if (n != null && n.signum() > 0 && n <= java.math.BigInteger.valueOf(maxValues.toLong()))
        return (0 until n.toInt())
          .map { k ->
            when (c) {
              is BvLitExpr ->
                BvUtils.bigIntegerToNeutralBvLitExpr(
                    java.math.BigInteger.valueOf(k.toLong()),
                    c.type.size,
                  )
                  .let { if (c.type.signedness != null) Bv(it.value, c.type.signedness) else it }
              else -> IntExprs.Int(k)
            }
          }
          .toSet()
    }
    // other operators: evaluate over the combinations of the atoms' values
    val atoms = mutableListOf<Expr<*>>()
    fun collect(x: Expr<*>) {
      if (x.lit() != null) return
      if (x is RefExpr<*> || x is Dereference<*, *, *>) {
        if (x !in atoms) atoms.add(x)
      } else x.ops.forEach { collect(it) }
    }
    collect(e)
    val atomValues = atoms.map { values(it, depth + 1)?.toList() ?: return null }
    if (atomValues.fold(1L) { acc, l -> acc * l.size } > maxValues) return null
    val result = mutableSetOf<LitExpr<*>>()
    fun go(i: Int, subst: Map<Expr<*>, LitExpr<*>>) {
      if (i == atoms.size) {
        fun sub(x: Expr<*>): Expr<*> = subst[x] ?: x.withOps(x.ops.map { sub(it) })
        sub(e).lit()?.let { result.add(it) }
          ?: run {
            result.clear()
            throw IllegalStateException()
          }
        return
      }
      for (v in atomValues[i]) go(i + 1, subst + (atoms[i] to v))
    }
    return try {
      go(0, emptyMap())
      result
    } catch (ex: IllegalStateException) {
      null
    }
  }

  private fun computeValueSets(xcfa: XcfaBuilder) {
    // inside non-deterministic branches too: every write counts, whichever branch it is on
    val stmts = xcfa.getProcedures().flatMap { p -> p.getEdges().flatMap { deepLabels(it.label) } }
    val globals = xcfa.getVars().associateBy { it.wrappedVar }
    // variables written by anything but a plain assignment are unknown
    val assigned = mutableMapOf<VarDecl<*>, MutableList<Expr<*>>>()
    val unknownVars = mutableSetOf<VarDecl<*>>()
    val memWrites = mutableListOf<MemoryAssignStmt<*, *, *>>()
    for (l in stmts) {
      val st = (l as? StmtLabel)?.stmt
      when {
        st is AssignStmt<*> -> assigned.getOrPut(st.varDecl) { mutableListOf() }.add(st.expr)
        st is MemoryAssignStmt<*, *, *> -> memWrites.add(st)
        st is HavocStmt<*> -> unknownVars.add(st.varDecl)
        st is AssumeStmt -> {}
        else -> unknownVars.addAll(l.collectVarsWithAccessType().filter { it.value.isWritten }.keys)
      }
    }
    // a started thread's parameters get the start label's arguments
    val startParams = mutableSetOf<VarDecl<*>>()
    for (l in stmts.filterIsInstance<StartLabel>()) {
      val proc = xcfa.getProcedures().find { it.name == l.name } ?: continue
      proc
        .getParams()
        .filter { it.second != ParamDirection.OUT }
        .forEachIndexed { i, (v, _) ->
          val arg = l.params.getOrNull(i + 1) ?: return@forEachIndexed
          assigned.getOrPut(v) { mutableListOf() }.add(arg)
          startParams.add(v)
        }
    }
    val liveAtStart = xcfa.getProcedures().flatMap { valueLiveAtStart(it) }.toSet() - startParams
    val allVars = assigned.keys + unknownVars
    for (v in allVars) {
      varValues[v] =
        when {
          v in unknownVars -> null
          v in globals ->
            globals[v]!!.initValue?.let { mutableSetOf(it) }
              ?: if (DereferenceToArrayPass.zeroInitialized) mutableSetOf(v.type.defaultValue)
              else null
          v in liveAtStart -> null // a local read before its first assignment
          else -> mutableSetOf()
        }
    }
    // constant cells start from their initial value
    memWrites.forEach { m ->
      m.deref.cell()?.let { c ->
        cellValues.putIfAbsent(
          c,
          if (DereferenceToArrayPass.zeroInitialized) mutableSetOf(c.key.elemType.defaultValue)
          else null,
        )
      }
    }
    var changed = true
    var rounds = 0
    // every set only grows, and a set over [maxValues] becomes unknown: this terminates
    while (changed) {
      if (rounds++ > 100_000) {
        // safety net only: never use a set that has not converged
        varValues.keys.forEach { varValues[it] = null }
        cellValues.keys.forEach { cellValues[it] = null }
        break
      }
      changed = false
      for ((v, exprs) in assigned) {
        if (varValues[v] == null) continue
        var acc: MutableSet<LitExpr<*>>? = varValues[v]
        for (e in exprs) acc = union(acc, values(e))
        if (acc != varValues[v]) {
          varValues[v] = acc
          changed = true
        }
      }
      for (m in memWrites) {
        val bases = values(m.deref.array)
        val offs = values(m.deref.offset)
        val vals = values(m.expr)
        val targets =
          if (bases == null || offs == null)
            cellValues.keys.filter { it.key == m.deref.memoryTypeKey }
          else bases.flatMap { b -> offs.map { o -> Cell(m.deref.memoryTypeKey, b, o) } }
        for (c in targets) {
          if (c in cellValues && cellValues[c] == null) continue
          val acc = union(cellValues[c] ?: mutableSetOf(), vals)
          if (acc != cellValues[c]) {
            cellValues[c] = acc
            changed = true
          }
        }
      }
    }
  }

  /**
   * Variables whose value at the start of [p] can reach an assignment or a memory access. Reads in
   * assumptions do not count: they only restrict paths (the frontend's range assumption on a fresh
   * declaration would otherwise make every such local look read before written).
   */
  private fun valueLiveAtStart(p: XcfaProcedureBuilder): Set<VarDecl<*>> {
    fun step(label: XcfaLabel, liveOut: Set<VarDecl<*>>): Set<VarDecl<*>> =
      when (label) {
        is SequenceLabel -> label.labels.foldRight(liveOut) { l, acc -> step(l, acc) }
        is NondetLabel -> label.labels.flatMap { step(it, liveOut) }.toSet()
        is StmtLabel ->
          when (val st = label.stmt) {
            is AssumeStmt -> liveOut
            is AssignStmt<*> ->
              (liveOut - st.varDecl) + hu.bme.mit.theta.core.utils.ExprUtils.getVars(st.expr)
            is HavocStmt<*> -> liveOut - st.varDecl
            else -> liveOut + label.collectVarsWithAccessType().keys
          }
        else -> liveOut + label.collectVarsWithAccessType().keys
      }
    val live = mutableMapOf<XcfaLocation, Set<VarDecl<*>>>()
    val work = ArrayDeque(p.getLocs())
    while (work.isNotEmpty()) {
      val loc = work.removeFirst()
      val out =
        loc.outgoingEdges
          .flatMap { e -> step(e.label, live[e.target] ?: emptySet<VarDecl<*>>()) }
          .toSet()
      if (out != (live[loc] ?: emptySet<VarDecl<*>>())) {
        live[loc] = out
        loc.incomingEdges.forEach { if (it.source !in work) work.addLast(it.source) }
      }
    }
    return live[p.initLoc] ?: emptySet<VarDecl<*>>()
  }

  /**
   * The literal bases [d] may use, or null if unknown. The null pointer is left out: dereferencing
   * it is undefined, and an access whose base matches no candidate reads the unknown value anyway.
   */
  private fun Dereference<*, *, *>.bases(): Set<LitExpr<*>>? =
    values(array)?.filter { it != array.type.defaultValue }?.toSet()

  private fun deepLabels(l: XcfaLabel): List<XcfaLabel> =
    when (l) {
      is SequenceLabel -> l.labels.flatMap { deepLabels(it) }
      is NondetLabel -> l.labels.flatMap { deepLabels(it) }
      else -> listOf(l)
    }

  private fun init(xcfa: XcfaBuilder) {
    computeValueSets(xcfa)
    val all = xcfa.getProcedures().flatMap { p -> p.getEdges().flatMap { it.label.dereferences } }
    val byKey = all.groupBy { it.memoryTypeKey }
    // accesses inside call, start or return labels cannot get the case split: keep those arrays
    val inOtherLabels =
      xcfa
        .getProcedures()
        .flatMap { p -> p.getEdges().flatMap { it.getFlatLabels() } }
        .filter { it !is StmtLabel }
        .flatMap { it.dereferences }
        .map { it.memoryTypeKey }
        .toSet()
    val map = linkedMapOf<Cell, VarDecl<*>>()
    val inits = mutableListOf<StmtLabel>()
    var i = 0
    for ((key, derefs) in byKey) {
      if (key in inOtherLabels) continue
      if (derefs.any { it.bases() == null }) continue // some base is unknown: keep the array
      // every cell an access may reach gets a variable, so a read never falls back to an unknown
      // value: a variable offset needs a bounded set of values, or the partition stays an array
      val offsetSets = derefs.map { d -> d.offset.lit()?.let { setOf(it) } ?: values(d.offset) }
      if (offsetSets.any { it == null }) continue
      val reach =
        derefs
          .zip(offsetSets)
          .flatMap { (d, offs) -> d.bases()!!.flatMap { b -> offs!!.map { o -> Cell(key, b, o) } } }
          .toSet()
      if (reach.size > maxCells) continue
      reach.forEach { c ->
        val v = Decls.Var("__cell${round}_${i++}", key.elemType)
        map[c] = v
        cellsOfBase.getOrPut(key to c.base) { mutableListOf() }.add(c)
        inits.add(xcfa.addGlobal(v))
      }
      if (
        derefs.any { it.offset.lit() == null || it.bases()!!.size != 1 || it.array.lit() == null }
      ) {
        val h =
          Helpers(
            Decls.Var("__cell${round}_unknown_$i", key.elemType),
            Decls.Var("__cell${round}_base_$i", key.arrayType),
            Decls.Var("__cell${round}_offset_$i", key.offsetType),
            Decls.Var("__cell${round}_value_$i", key.elemType),
          )
        i++
        helpers[key] = h
        listOf(h.unknown, h.base, h.offset, h.value).forEach { inits.add(xcfa.addGlobal(it)) }
      }
      eligible.add(key)
    }
    if (inits.isNotEmpty()) {
      xcfa.getInitProcedures().forEach { (procedure, _) ->
        procedure.initLoc.outgoingEdges.toSet().forEach { edge ->
          procedure.removeEdge(edge)
          procedure.addEdge(edge.withLabel(SequenceLabel(inits + listOf(edge.label))))
        }
      }
    }
    cells = map
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (cells == null) {
      init(builder.parent)
      // all procedures at once: a later pass (DereferenceToArrayPass) collects the memory types of
      // every procedure on its first run, and must not see the accesses that become variables here
      if (eligible.isNotEmpty()) builder.parent.getProcedures().forEach { rewrite(it) }
    }
    return builder
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

  /** Cells [d] may access, each with the condition (on [base] and [off]) selecting it. */
  private fun Dereference<*, *, *>.candidates(
    base: Expr<*>,
    off: Expr<*>,
  ): List<Pair<VarDecl<*>, Expr<hu.bme.mit.theta.core.type.booltype.BoolType>>> {
    val bs = bases()!!
    val k = offset.lit()
    return bs.flatMap { b ->
      val cs =
        if (k != null) listOf(Cell(memoryTypeKey, b, k))
        else cellsOfBase[memoryTypeKey to b] ?: emptyList()
      cs.mapNotNull { c ->
        val v = cells!![c] ?: return@mapNotNull null
        val conds =
          listOfNotNull(
            if (array.lit() == null) Eq(base, b) else null,
            if (k == null) Eq(off, c.offset) else null,
          )
        v to And(conds)
      }
    }
  }

  /** A single unconditional cell for [d], if it has one. */
  private fun Dereference<*, *, *>.direct(): VarDecl<*>? {
    val bs = bases() ?: return null
    val k = offset.lit() ?: return null
    if (bs.size != 1 || array.lit() == null) return null
    return cells!![Cell(memoryTypeKey, bs.first(), k)]
  }

  private fun stmts(list: List<Stmt>, label: StmtLabel): XcfaLabel =
    if (list.size == 1) StmtLabel(list[0], label.choiceType, label.metadata)
    else SequenceLabel(list.map { StmtLabel(it, label.choiceType, label.metadata) }, label.metadata)

  private fun reset(v: VarDecl<*>): Stmt =
    AssignStmt.of(cast(v, v.type), cast(v.type.defaultValue, v.type))

  private fun XcfaLabel.scalarize(): XcfaLabel =
    when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.scalarize() }, metadata)
      is NondetLabel -> NondetLabel(labels.map { it.scalarize() }.toSet(), metadata)
      is StmtLabel -> {
        val unknowns = linkedSetOf<VarDecl<*>>()
        val core: List<Stmt> =
          when (stmt) {
            is MemoryAssignStmt<*, *, *> -> {
              val deref = stmt.deref
              val value = stmt.expr.scalarize(unknowns)
              if (deref.memoryTypeKey !in eligible) {
                listOf(
                  MemoryAssignStmt.create(deref.scalarize(unknowns) as Dereference<*, *, *>, value)
                )
              } else {
                val direct = deref.direct()
                if (direct != null)
                  listOf(AssignStmt.of(cast(direct, direct.type), cast(value, direct.type)))
                else {
                  val h = helpers[deref.memoryTypeKey]!!
                  val base = deref.array.scalarize(unknowns)
                  val off = deref.offset.scalarize(unknowns)
                  listOf(
                    AssignStmt.of(cast(h.base, h.base.type), cast(base, h.base.type)),
                    AssignStmt.of(cast(h.offset, h.offset.type), cast(off, h.offset.type)),
                    AssignStmt.of(cast(h.value, h.value.type), cast(value, h.value.type)),
                  ) +
                    deref.candidates(h.base.ref, h.offset.ref).map { (v, cond) ->
                      AssignStmt.of(
                        cast(v, v.type),
                        Ite(cond, cast(h.value.ref, v.type), cast(v.ref, v.type)),
                      )
                    } +
                    listOf(reset(h.base), reset(h.offset), reset(h.value))
                }
              }
            }
            is AssignStmt<*> ->
              listOf(
                AssignStmt.of(
                  cast(stmt.varDecl, stmt.varDecl.type),
                  cast(stmt.expr.scalarize(unknowns), stmt.varDecl.type),
                )
              )
            is AssumeStmt -> listOf(AssumeStmt.of(stmt.cond.scalarize(unknowns)))
            else -> listOf(stmt)
          }
        val all = unknowns.map { HavocStmt.of(it) } + core + unknowns.map { reset(it) }
        if (all.size == 1 && all[0] == stmt) this else stmts(all, this)
      }
      is InvokeLabel ->
        InvokeLabel(
          name,
          params.map { it.scalarize(null) },
          metadata,
          tempLookup,
          isLibraryFunction,
        )
      is StartLabel ->
        StartLabel(name, params.map { it.scalarize(null) }, pidVar, metadata, tempLookup)
      is ReturnLabel -> ReturnLabel(enclosedLabel.scalarize())
      else -> this
    }

  /** [unknowns] collects the nondeterministic helpers read; null where none may be needed. */
  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> Expr<T>.scalarize(unknowns: MutableSet<VarDecl<*>>?): Expr<T> {
    if (this is Dereference<*, *, *> && memoryTypeKey in eligible) {
      direct()?.let {
        return cast(it.ref, type)
      }
      val h = helpers[memoryTypeKey]!!
      if (unknowns != null) {
        unknowns.add(h.unknown)
        val base = array.scalarize(unknowns)
        val off = offset.scalarize(unknowns)
        var result: Expr<*> = h.unknown.ref
        for ((v, cond) in candidates(base, off).reversed()) {
          result = Ite(cond, cast(v.ref, type), cast(result, type))
        }
        return cast(result, type)
      }
    }
    return withOps(ops.map { it.scalarize(unknowns) })
  }
}
