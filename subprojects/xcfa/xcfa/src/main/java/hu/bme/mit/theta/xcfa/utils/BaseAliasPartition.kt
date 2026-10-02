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
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger

/**
 * Partitions the memory objects of an XCFA so that dereferences whose bases can never hold the same
 * object id fall into different partitions. Two dereferences of different partitions never address
 * the same cell, so each partition can have its own backing memory.
 *
 * The analysis is a flow-insensitive points-to analysis over base *values*: for every variable it
 * over-approximates the set of object ids the variable can hold. An object is a literal base id, a
 * heap allocation site, or unknown. Runtime ids come from the `__malloc` counter, which by
 * construction never hands out a compile-time id (see [POINTER_BASE_CLASSES]). Each allocation
 * reads the counter right after advancing it, so two allocation sites never return the same id:
 * when every read of the counter follows this pattern, each site is a separate object, otherwise
 * the whole heap is one object. A value that the analysis cannot follow is unknown: a havoc, a read
 * of a possibly uninitialized variable, a global without an initial value, or an expression other
 * than a literal, a variable, an ite, or a value stored in memory. All values stored in memory are
 * pooled, so a base loaded from memory may be any of them, or the initial content of a cell that
 * was never written.
 *
 * Soundness does not rely on the shape of the base expressions: the same cell reached through a
 * pointer variable and through its constant-folded base literal lands in the same partition,
 * because the literal flows into the variable. If any dereference may use an unknown base, it may
 * address any object, so no split is made at all ([compute] returns null).
 */
class BaseAliasPartition private constructor(private val classOfBase: (Expr<*>) -> Int) {

  /** The partition of a dereference. */
  fun partitionOf(deref: Dereference<*, *, *>): Int = classOfBase(deref.array)

  private sealed interface Obj

  private data class Lit(val id: BigInteger) : Obj

  /** The ids returned by one allocation site; [ANY_SITE] stands for every site. */
  private data class Heap(val site: Int) : Obj

  private data object Unknown : Obj

  companion object {
    private const val MALLOC_VAR_NAME = "__malloc"
    private const val ANY_SITE = -1

    /**
     * Computes the partition of [xcfa], or null when the memory cannot be split. [zeroInitialized]
     * tells whether memory cells start as zero; otherwise they start with arbitrary values.
     */
    fun compute(xcfa: XcfaBuilder, zeroInitialized: Boolean): BaseAliasPartition? =
      Analysis(xcfa, zeroInitialized).run()

    private class Analysis(private val xcfa: XcfaBuilder, zeroInitialized: Boolean) {
      private val pts = LinkedHashMap<VarDecl<*>, MutableSet<Obj>>()
      private val stored =
        LinkedHashSet<Obj>(listOf(if (zeroInitialized) Lit(BigInteger.ZERO) else Unknown))
      private val labels =
        xcfa.getProcedures().flatMap { p -> p.getEdges().flatMap { it.label.flat() } }
      private val sites: Map<AssignStmt<*>, Int>? = allocationSites()

      fun run(): BaseAliasPartition? {
        seed()
        do {
          var changed = false
          fun flow(v: VarDecl<*>, e: Expr<*>) {
            changed = pts.getOrPut(v) { LinkedHashSet() }.addAll(value(e)) || changed
          }
          labels.forEach { label ->
            when (label) {
              is StmtLabel ->
                when (val stmt = label.stmt) {
                  is AssignStmt<*> ->
                    sites?.get(stmt)?.let {
                      changed =
                        pts.getOrPut(stmt.varDecl) { LinkedHashSet() }.add(Heap(it)) || changed
                    } ?: flow(stmt.varDecl, stmt.expr)
                  is MemoryAssignStmt<*, *, *> ->
                    changed = stored.addAll(value(stmt.expr)) || changed
                  else -> {}
                }
              is InvokeLabel -> bind(label.name, label.params, ::flow)
              is StartLabel -> bind(label.name, label.params, ::flow)
              else -> {}
            }
          }
        } while (changed)

        val bases = labels.flatMap { it.dereferences }.map { it.array }.toSet()
        val objects = bases.associateWith { value(it) }
        if (objects.values.any { it.isEmpty() || Unknown in it }) return null

        val uf = UnionFind<Obj>()
        objects.values.forEach { objs -> objs.reduce { a, b -> a.also { uf.union(a, b) } } }
        val all = objects.values.flatten().toSet()
        if (Heap(ANY_SITE) in all)
          all.filterIsInstance<Heap>().forEach { uf.union(it, Heap(ANY_SITE)) }
        val ids = LinkedHashMap<Obj, Int>()
        val classes =
          objects.mapValues { (_, objs) -> ids.getOrPut(uf.find(objs.first())) { ids.size } }
        return BaseAliasPartition { base ->
          classes[base] ?: error("Base $base was not part of the alias analysis")
        }
      }

      /**
       * The allocation sites: assignments of a counter value to another variable. Null when some
       * site does not directly follow an advance of the counter in the same edge, as then two sites
       * might return the same id.
       */
      private fun allocationSites(): Map<AssignStmt<*>, Int>? {
        val sites = LinkedHashMap<AssignStmt<*>, Int>()
        val runs = xcfa.getProcedures().flatMap { p -> p.getEdges().flatMap { it.label.runs() } }
        runs.forEach { flat ->
          flat.forEachIndexed { i, label ->
            val stmt = (label as? StmtLabel)?.stmt as? AssignStmt<*> ?: return@forEachIndexed
            if (stmt.varDecl.name == MALLOC_VAR_NAME || !stmt.expr.isHeapValue())
              return@forEachIndexed
            val previous = (flat.getOrNull(i - 1) as? StmtLabel)?.stmt as? AssignStmt<*>
            if (previous?.varDecl?.name != MALLOC_VAR_NAME || !previous.expr.isHeapValue())
              return null
            sites.getOrPut(stmt) { sites.size }
          }
        }
        return sites
      }

      private fun Expr<*>.isHeapValue(): Boolean =
        ExprUtils.getVars(this).map { it.name }.toSet() == setOf(MALLOC_VAR_NAME) &&
          derefs().isEmpty()

      /**
       * Unknown values: havocs and possibly uninitialized reads. The monolithic encodings do not
       * use the initial value of a global, so a global is uninitialized until the init procedure
       * assigns it.
       */
      private fun seed() {
        labels.forEach {
          if (it is StmtLabel && it.stmt is HavocStmt<*>)
            pts.getOrPut((it.stmt as HavocStmt<*>).varDecl) { LinkedHashSet() }.add(Unknown)
        }
        xcfa.getVars().forEach { global ->
          val objs = pts.getOrPut(global.wrappedVar) { LinkedHashSet() }
          global.initValue?.let { objs.addAll(value(it)) } ?: objs.add(Unknown)
        }
        val globals = xcfa.getVars().map { it.wrappedVar }.toSet()
        // without a known entry point, any procedure may run first
        val initProcs =
          xcfa.getInitProcedures().map { it.first }.toSet().ifEmpty { xcfa.getProcedures() }
        xcfa.getProcedures().forEach { proc ->
          val uninit = proc.getVars() + (if (proc in initProcs) globals else emptySet())
          proc.mayUninitReads(uninit, globals).forEach {
            pts.getOrPut(it) { LinkedHashSet() }.add(Unknown)
          }
        }
      }

      /** Binds the actual parameters of a call or thread start to the formal ones, both ways. */
      private fun bind(name: String, actuals: List<Expr<*>>, flow: (VarDecl<*>, Expr<*>) -> Unit) {
        val callee = xcfa.getProcedures().find { it.name == name } ?: return
        callee.getParams().forEachIndexed { i, (formal, dir) ->
          val actual = actuals.getOrNull(i) ?: return@forEachIndexed
          if (dir != ParamDirection.OUT) flow(formal, actual)
          if (dir != ParamDirection.IN && actual is RefExpr<*>)
            flow(actual.decl as VarDecl<*>, formal.ref)
        }
      }

      private fun value(e: Expr<*>): Set<Obj> =
        when (e) {
          is LitExpr<*> -> setOf(litObj(e))
          is RefExpr<*> ->
            if (e.decl.name == MALLOC_VAR_NAME) setOf(Heap(ANY_SITE))
            else (e.decl as? VarDecl<*>)?.let { pts[it] }.orEmpty()
          is Dereference<*, *, *> -> stored
          is IteExpr<*> -> value(e.then) + value(e.`else`)
          is PosExpr<*> -> value(e.op)
          is ModExpr<*> -> value(e.ops[0])
          else -> if (e.isHeapValue()) setOf(Heap(ANY_SITE)) else setOf(Unknown)
        }

      private fun litObj(e: LitExpr<*>): Obj =
        when (e) {
          is IntLitExpr -> Lit(e.value)
          is BvLitExpr -> Lit(BvUtils.neutralBvLitExprToBigInteger(e))
          else -> Unknown
        }
    }

    private fun XcfaLabel.flat(): List<XcfaLabel> =
      when (this) {
        is SequenceLabel -> labels.flatMap { it.flat() }
        is NondetLabel -> labels.flatMap { it.flat() }
        is ReturnLabel -> enclosedLabel.flat()
        else -> listOf(this)
      }

    /** Sequences of labels that execute right after each other; a nondet choice ends a run. */
    private fun XcfaLabel.runs(): List<List<XcfaLabel>> {
      val runs = mutableListOf<List<XcfaLabel>>()
      var current = mutableListOf<XcfaLabel>()
      fun walk(label: XcfaLabel) {
        when (label) {
          is SequenceLabel -> label.labels.forEach(::walk)
          is ReturnLabel -> walk(label.enclosedLabel)
          is NondetLabel -> {
            runs.add(current)
            current = mutableListOf()
            label.labels.forEach { runs.addAll(it.runs()) }
          }
          else -> current.add(label)
        }
      }
      walk(this)
      runs.add(current)
      return runs
    }

    private fun Expr<*>.derefs(): List<Dereference<*, *, *>> =
      (if (this is Dereference<*, *, *>) listOf(this) else listOf()) + ops.flatMap { it.derefs() }

    /**
     * Variables read while possibly holding no assigned value yet, along some path, starting with
     * the variables [uninit] unassigned. Globals still unassigned at a thread start count as read,
     * as the started thread may read them.
     */
    private fun XcfaProcedureBuilder.mayUninitReads(
      uninit: Set<VarDecl<*>>,
      globals: Set<VarDecl<*>>,
    ): Set<VarDecl<*>> {
      val result = LinkedHashSet<VarDecl<*>>()
      fun walk(label: XcfaLabel, before: Set<VarDecl<*>>): Set<VarDecl<*>> =
        when (label) {
          is SequenceLabel -> label.labels.fold(before) { acc, it -> walk(it, acc) }
          is NondetLabel -> label.labels.map { walk(it, before) }.fold(emptySet()) { a, b -> a + b }
          is ReturnLabel -> walk(label.enclosedLabel, before)
          else -> {
            val access = label.collectVarsWithAccessType()
            result.addAll(access.filter { it.value.isRead }.keys intersect before)
            if (label is StartLabel) result.addAll(before intersect globals)
            before - access.filter { it.value.isWritten }.keys
          }
        }
      val uninitAt = mutableMapOf(initLoc to uninit)
      val waitlist = ArrayDeque(listOf(initLoc))
      while (waitlist.isNotEmpty()) {
        val loc = waitlist.removeFirst()
        loc.outgoingEdges.forEach { edge ->
          val after = walk(edge.label, uninitAt[loc]!!)
          val old = uninitAt[edge.target]
          val new = (old ?: emptySet()) union after
          if (old != new) {
            uninitAt[edge.target] = new
            waitlist.add(edge.target)
          }
        }
      }
      return result
    }
  }

  private class UnionFind<T> {
    private val parent = LinkedHashMap<T, T>()

    fun find(x: T): T {
      val p = parent.getOrPut(x) { x }
      return if (p == x) x else find(p).also { parent[x] = it }
    }

    fun union(a: T, b: T) {
      val ra = find(a)
      val rb = find(b)
      if (ra != rb) parent[ra] = rb
    }
  }
}
