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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.analysis.algorithm.oc.EventType.READ
import hu.bme.mit.theta.analysis.algorithm.oc.EventType.WRITE
import hu.bme.mit.theta.analysis.algorithm.oc.Relation
import hu.bme.mit.theta.analysis.algorithm.oc.RelationType
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprSimplifier
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.references

internal class XcfaToEventGraph(private val xcfa: XCFA) {

  init {
    if (xcfa.initProcedures.size > 1) exit("multiple entry points.")
  }

  data class EventGraph(
    val threads: Set<Thread>,
    val events: Map<VarDecl<*>, Map<Int, List<E>>>,
    val pos: List<R>, // not transitively closed!
    val rfs: Map<VarDecl<*>, Set<R>>,
    val wss: Map<VarDecl<*>, Set<R>>,
    val violations: List<Violation>, // OR!
    val branchingConditions: List<Expr<BoolType>>,
    val memoryDecl: VarDecl<IntType>,
    val memoryGarbage: IndexedConstDecl<IntType>,
  )

  private val threads = mutableSetOf<Thread>()
  private var indexing = VarIndexingFactory.indexing(0)
  private val localVars = mutableMapOf<VarDecl<*>, MutableMap<Int, VarDecl<*>>>()

  private val events: MutableMap<VarDecl<*>, MutableMap<Int, MutableList<E>>> = mutableMapOf()
  private val pos: MutableList<R> = mutableListOf()
  private val rfs: MutableMap<VarDecl<*>, MutableSet<R>> = mutableMapOf()
  private var wss = mutableMapOf<VarDecl<*>, MutableSet<R>>()
  private val violations: MutableList<Violation> = mutableListOf()
  private val branchingConditions: MutableList<Expr<BoolType>> = mutableListOf()

  private val memoryDecl: VarDecl<IntType> = Decls.Var("__oc_memory_declaration__", Int())
  private val memoryGarbage = // the value of this declaration is not constrained
    memoryDecl.getNewIndexed().also { XcfaEvent.memoryGarbage = it }

  fun create(): EventGraph {
    ThreadProcessor(Thread(procedure = xcfa.initProcedures.first().first), true).process()
    addCrossThreadRelations()
    return EventGraph(
      threads,
      events,
      pos,
      rfs,
      wss,
      violations,
      branchingConditions,
      memoryDecl,
      memoryGarbage,
    )
  }

  private fun addCrossThreadRelations() {
    for ((v, map) in events) {
      if (map.values.all { it.all { e -> e.assignment == null } })
        exit("variable $v is not initialized")
      for ((pid1, list1) in map) for ((pid2, list2) in map) if (pid1 != pid2)
        for (e1 in list1.filter { it.type == WRITE }) for (e2 in list2) {
          if (e2.type == READ) rfs.add(RelationType.RF, e1, e2)
          if (e2.type == WRITE) wss.add(RelationType.WS, e1, e2)
        }
    }
  }

  private inner class ThreadProcessor(
    private val thread: Thread,
    addMemoryGarbage: Boolean = false,
  ) {

    private val pid = thread.pid
    private var last = listOf<E>()
    private var guard = setOf<Expr<BoolType>>()
    private lateinit var lastWrites: MutableMap<VarDecl<*>, Set<E>>
    private val memoryWrites = mutableSetOf<E>()
    private lateinit var edge: XcfaEdge
    private var inEdge = false
    private var atomicBlock: Int? = null
    private val multipleUsePidVars = mutableSetOf<VarDecl<*>>()

    init {
      if (addMemoryGarbage) {
        val firstEdge = thread.procedure.initLoc.outgoingEdges.first()
        val e = E(memoryGarbage, WRITE, setOf(), pid, firstEdge, E.uniqueClkId())
        e.assignment = True()
        memoryWrites.add(e)
        events
          .getOrPut(memoryDecl) { mutableMapOf() }
          .getOrPut(thread.pid) { mutableListOf() }
          .add(e)
        last = listOf(e)
      }
    }

    private fun event(d: VarDecl<*>, type: EventType, varPid: Int? = null): List<E> {
      check(!inEdge || last.size == 1)
      val decl = d.threadVar(varPid ?: pid)
      val clkId =
        when {
          inEdge -> last.first().clkId
          atomicBlock != null -> atomicBlock!!
          else -> E.uniqueClkId()
        }
      val e = E(decl.getNewIndexed(), type, guard, pid, edge, clkId)
      last.forEach { po(it, e) }
      inEdge = true
      when (type) {
        READ -> lastWrites[decl]?.forEach { rfs.add(RelationType.RF, it, e) }
        WRITE -> lastWrites[decl] = setOf(e)
      }
      events.getOrPut(decl) { mutableMapOf() }.getOrPut(pid) { mutableListOf() }.add(e)
      return listOf(e)
    }

    private fun memoryEvent(
      deref: Dereference<*, *, *>,
      consts: Map<Any, IndexedConstDecl<*>>,
      type: EventType,
      useProvidedConst: Boolean = false,
    ): List<E> {
      check(!inEdge || last.size == 1)
      val array = deref.array.with(consts)
      val offset = deref.offset.with(consts)
      val clkId =
        when {
          inEdge -> last.first().clkId
          atomicBlock != null -> atomicBlock!!
          else -> E.uniqueClkId()
        }
      val const =
        if (useProvidedConst && deref in consts) {
          consts[deref]!!
        } else {
          memoryDecl.getNewIndexed()
        }
      val e = E(const, type, guard, pid, edge, clkId, array, offset)
      last.forEach { po(it, e) }
      inEdge = true
      when (type) {
        READ -> memoryWrites.forEach { rfs.add(RelationType.RF, it, e) }
        WRITE -> memoryWrites.add(e)
      }
      events.getOrPut(memoryDecl) { mutableMapOf() }.getOrPut(pid) { mutableListOf() }.add(e)
      return listOf(e)
    }

    private fun <T : Type> Expr<T>.toEvents(
      consts: Map<Any, IndexedConstDecl<*>>? = null,
      useProvidedConst: Boolean = false,
    ): Map<Any, IndexedConstDecl<*>> {
      val mutConsts = consts?.toMutableMap() ?: mutableMapOf()
      vars.forEach {
        last = event(it, READ)
        if (!useProvidedConst) mutConsts[it] = last.first().const
      }
      dereferences.forEach {
        last = memoryEvent(it, mutConsts, READ, useProvidedConst)
        if (!useProvidedConst) mutConsts[it] = last.first().const
      }
      return mutConsts
    }

    fun process() {
      threads.add(thread)
      val waitList = mutableSetOf<SearchItem>()
      val toVisit =
        mutableSetOf(
          SearchItem(thread.procedure.initLoc).apply {
            guards.add(thread.guard)
            thread.startEvent?.let { lastEvents.add(it) }
            this.lastWrites.add(thread.lastWrites)
            lastEvents.addAll(last)
          }
        )

      while (toVisit.isNotEmpty()) {
        val current = toVisit.first()
        toVisit.remove(current)
        check(current.incoming == current.loc.incomingEdges.size)
        check(current.incoming == current.guards.size || current.loc.initial)
        // lastEvents intentionally skipped
        check(current.incoming == current.lastWrites.size || current.loc.initial)
        check(current.incoming == current.threadLookups.size)
        check(current.incoming == current.atomics.size)
        check(
          current.atomics.all { it == current.atomics.first() } ||
            current.loc.error ||
            (current.loc.outgoingEdges.let {
              it.size == 1 &&
                it.first().let { e -> e.label.getFlatLabels().isEmpty() && e.target.error }
            })
        )

        if (current.loc.error) {
          val errorGuard = Or(current.guards.map { it.toAnd() })
          violations.add(Violation(current.loc, pid, errorGuard, current.lastEvents))
          continue
        }

        if (current.loc.final) {
          thread.finalEvents.addAll(current.lastEvents)
        }

        val mergedGuard = current.guards.toOrInSet()
        val assumeConsts = mutableMapOf<Any, MutableList<ConstDecl<*>>>()

        for (e in current.loc.outgoingEdges) {
          edge = e
          inEdge = false
          last = current.lastEvents
          // intersection of guards of incoming edges:
          guard = mergedGuard
          lastWrites = current.lastWrites.merge().toMutableMap()
          val threadLookup =
            current.threadLookups
              .merge { s1, s2 ->
                s1 + s2.filter { (guard2, _) -> s1.none { (guard1, _) -> guard1 == guard2 } }
              }
              .toMutableMap()
          var firstLabel = true
          atomicBlock = current.atomics.firstOrNull()

          edge.getFlatLabels().forEach { label ->
            if (label.references.isNotEmpty()) exit("references")
            when (label) {
              is StmtLabel -> {
                when (val stmt = label.stmt) {
                  is AssignStmt<*> -> stmt.process()
                  is AssumeStmt -> stmt.process(assumeConsts, firstLabel)
                  is HavocStmt<*> -> stmt.process()
                  is MemoryAssignStmt<*, *, *> -> stmt.process()
                  is SkipStmt -> {}
                  else -> exit("unknown statement type: $stmt")
                }
              }

              is StartLabel -> label.process(threadLookup)
              is JoinLabel -> label.process(threadLookup)
              is FenceLabel -> label.process()
              is InvokeLabel -> label.process()
              is NopLabel -> {}
              else -> exit("unsupported label type: $label")
            }
            firstLabel = false
          }

          val searchItem =
            waitList.find { it.loc == edge.target }
              ?: SearchItem(edge.target).apply { waitList.add(this) }
          searchItem.guards.add(guard)
          searchItem.lastEvents.addAll(last)
          searchItem.lastWrites.add(lastWrites)
          searchItem.threadLookups.add(threadLookup)
          searchItem.atomics.add(atomicBlock)
          searchItem.incoming++
          if (searchItem.incoming == searchItem.loc.incomingEdges.size) {
            waitList.remove(searchItem)
            toVisit.add(searchItem)
          }
        }

        if (current.loc.outgoingEdges.size > 1) {
          for (e in current.loc.outgoingEdges) {
            val first = e.getFlatLabels().first()
            if (first !is StmtLabel || first.stmt !is AssumeStmt) {
              exit("branching with non-assume labels")
            }
          }
          assumeConsts.forEach { (_, set) ->
            for ((i1, v1) in set.withIndex()) for ((i2, v2) in set.withIndex()) {
              if (i1 == i2) break
              branchingConditions.add(Eq(v1.ref, v2.ref))
            }
          }
        }
      }

      if (waitList.isNotEmpty()) exit("loops and dangling edges")
    }

    private fun AssignStmt<*>.process() {
      val consts = this.expr.toEvents()
      last = event(this.varDecl, WRITE)
      last.first().assignment = Eq(last.first().const.ref, this.expr.with(consts))
    }

    private fun AssumeStmt.process(
      assumeConsts: MutableMap<Any, MutableList<ConstDecl<*>>>,
      firstLabel: Boolean,
    ) {
      val consts =
        this.cond.vars.associateWith { it.threadVar(pid).getNewIndexed(false) } +
          this.cond.dereferences.associateWith { memoryDecl.getNewIndexed(true) }
      val condWithConsts = this.cond.with(consts)
      val asAssign =
        consts.size == 1 &&
          consts.keys.first().let { it is VarDecl<*> && it.threadVar(pid) !in lastWrites }
      if (edge.source.outgoingEdges.size > 1 || !asAssign) {
        guard = guard + condWithConsts
        if (firstLabel) {
          consts.forEach { (v, c) -> assumeConsts.getOrPut(v) { mutableListOf() }.add(c) }
        }
      }
      this.cond.toEvents(consts, true)
      if ((edge.source.outgoingEdges.size == 1 || !firstLabel) && asAssign) {
        last.first().assignment = condWithConsts
      }
    }

    private fun HavocStmt<*>.process() {
      last = event(this.varDecl, WRITE)
      last.first().assignment = True()
    }

    private fun MemoryAssignStmt<*, *, *>.process() {
      val exprConsts = this.expr.toEvents()
      val arrayConsts = this.deref.array.toEvents(exprConsts)
      val offsetConsts = this.deref.offset.toEvents(arrayConsts)
      last = memoryEvent(this.deref, arrayConsts + offsetConsts, WRITE)
      last.first().assignment = Eq(last.first().const.ref, this.expr.with(exprConsts))
    }

    private fun StartLabel.process(
      threadLookup: MutableMap<VarDecl<*>, Set<Pair<Set<Expr<BoolType>>, Thread>>>
    ) {
      if (this.name in thread.startHistory) {
        exit("recursive thread start")
      }
      val procedure =
        xcfa.procedures.find { it.name == this.name }
          ?: exit("unknown procedure name: ${this.name}")
      val newPid = Thread.uniqueId()

      // assign parameter
      val consts = this.params[1].toEvents()
      procedure.params
        .firstOrNull { it.second != ParamDirection.OUT }
        ?.first
        ?.let { arg ->
          last = event(arg, WRITE, newPid)
          last.first().assignment = Eq(last.first().const.ref, this.params[1].with(consts))
        }

      last = event(this.pidVar, WRITE)
      val pidVar = this.pidVar.threadVar(pid)
      if (threads.any { it.pidVar == pidVar }) {
        multipleUsePidVars.add(pidVar)
      }
      val newHistory = thread.startHistory + thread.procedure.name
      val newThread = Thread(newPid, procedure, guard, pidVar, last.first(), newHistory, lastWrites)
      last.first().assignment = Eq(last.first().const.ref, Int(newPid))
      threadLookup[pidVar] = setOf(Pair(guard, newThread))
      ThreadProcessor(newThread).process()
    }

    private fun JoinLabel.process(
      threadLookup: MutableMap<VarDecl<*>, Set<Pair<Set<Expr<BoolType>>, Thread>>>
    ) {
      val incomingGuard = guard
      val lastEvents = mutableListOf<E>()
      val joinGuards = mutableListOf<Set<Expr<BoolType>>>()
      val pidVar = this.pidVar.threadVar(pid)
      if (pidVar in multipleUsePidVars) {
        exit("join on a pthread_t variable used in multiple pthread_create calls")
      }
      threadLookup[pidVar]?.forEach { (g, thread) ->
        guard = incomingGuard + g + thread.finalEvents.map { it.guard }.toOrInSet()
        val joinEvent = event(this.pidVar, READ).first()
        thread.finalEvents.forEach { final -> po(final, joinEvent) }
        lastEvents.add(joinEvent)
        joinGuards.add(guard)
        thread.joinEvents.add(joinEvent)
      } ?: exit("thread started in a different thread")
      guard = joinGuards.toOrInSet()
      last = lastEvents
    }

    private fun FenceLabel.process() {
      if (this !is AtomicFenceLabel) {
        exit("untransformed fence label: $this")
      }
      if (this is AtomicBeginLabel) atomicBlock = E.uniqueClkId()
      if (this is AtomicEndLabel) atomicBlock = null
    }

    private fun InvokeLabel.process() {
      when (name) {
        "pthread_getspecific" -> {
          val ret = (params[0] as RefExpr<*>).decl as VarDecl<*>
          val key = (params[1] as Dereference<*, *, *>).array
          val deref = Dereference.of(key, Int(pid), Int())
          val assign = Assign(cast(ret, Int()), deref)
          assign.process()
        }

        "pthread_setspecific" -> {
          val ret = (params[0] as RefExpr<*>).decl as VarDecl<*>
          val key = (params[1] as Dereference<*, *, *>).array
          val deref = Dereference.of(key, Int(pid), Int())
          val memAssign = MemoryAssignStmt.of(deref, cast(params[2], Int()))
          memAssign.process()
          val assign = Assign(cast(ret, Int()), Int(0))
          assign.process()
        }

        "pthread_key_create" -> {
          val isNull = Eq(params[2], Int(0))
          if (ExprSimplifier.create().simplify(isNull, ImmutableValuation.empty()) != True()) {
            exit("pthread_key_create with non-null destructor")
          }
          val ret = (params[0] as RefExpr<*>).decl as VarDecl<*>
          val key = (params[1] as RefExpr<*>).decl as VarDecl<*>
          repeat(maxPid) { i ->
            val deref = Dereference.of(key.ref, Int(i), Int())
            val default = MemoryAssignStmt.of(deref, Int(0))
            default.process()
          }
          val assign = Assign(cast(ret, Int()), Int(0))
          assign.process()
        }

        else -> {
          if (xcfa.procedures.any { it.name == this.name }) {
            exit("OC checker requires function inlining: $this")
          }
          exit("Unknown function: $this")
        }
      }
    }
  }

  private fun po(from: E?, to: E) {
    from ?: return
    pos.add(Relation(RelationType.PO, from, to))
  }

  private fun <K, V> List<Map<K, Set<V>>>.merge(
    merge: (Set<V>, Set<V>) -> Set<V> = { a, b -> a + b }
  ) =
    reduce(mapOf()) { acc, map ->
      (acc.keys + map.keys).associateWith { k ->
        val set1 = acc[k] ?: setOf()
        val set2 = map[k] ?: setOf()
        merge(set1, set2)
      }
    }

  private inline fun <T> Collection<T>.reduce(default: T, operation: (T, T) -> T): T =
    if (isEmpty()) default else reduce(operation)

  private fun MutableMap<VarDecl<*>, MutableSet<R>>.add(type: RelationType, from: E, to: E) =
    getOrPut(from.const.varDecl) { mutableSetOf() }.add(Relation(type, from, to))

  private fun <T : Type> Expr<T>.with(consts: Map<Any, ConstDecl<*>>): Expr<T> =
    when (this) {
      is Dereference<*, *, T> -> consts[this]?.ref?.let { cast(it, type) } ?: this
      is RefExpr<T> -> consts[decl]?.ref?.let { cast(it, type) } ?: this
      else -> map { it.with(consts) }
    }

  private fun <T : Type> VarDecl<T>.getNewIndexed(increment: Boolean = true): IndexedConstDecl<T> {
    val constDecl = getConstDecl(indexing.get(this))
    if (increment) indexing = indexing.inc(this)
    return constDecl
  }

  private fun <T : Type> VarDecl<T>.threadVar(pid: Int): VarDecl<T> =
    if (this !== memoryDecl && xcfa.globalVars.none { it.wrappedVar == this && !it.threadLocal }) {
      // if not global var
      cast(
        localVars
          .getOrPut(this) { mutableMapOf() }
          .getOrPut(pid) { Decls.Var("t$pid::$name", type) },
        type,
      )
    } else this

  private val maxPid by lazy {
    var counter = 1
    fun explore(proc: XcfaProcedure, startHistory: Set<String>) {
      proc.edges.forEach { e ->
        e.getFlatLabels().filterIsInstance<StartLabel>().forEach { s ->
          if (s.name in startHistory) {
            exit("recursive thread start")
          }
          counter++
          val procedure =
            xcfa.procedures.find { it.name == s.name } ?: exit("unknown procedure name: ${s.name}")
          explore(procedure, startHistory + proc.name)
        }
      }
    }

    val initProc = xcfa.initProcedures.first().first
    explore(initProc, setOf(initProc.name))
    counter
  }

  private fun exit(msg: String): Nothing {
    error("Feature not supported by OC checker: $msg.")
  }
}
