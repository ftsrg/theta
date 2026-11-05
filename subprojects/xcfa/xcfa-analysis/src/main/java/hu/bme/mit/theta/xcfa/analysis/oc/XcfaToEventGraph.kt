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
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprSimplifier
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.UnrollCut
import hu.bme.mit.theta.xcfa.utils.MemoryTypeKey
import hu.bme.mit.theta.xcfa.utils.addressesAtomicData
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.integerOf
import hu.bme.mit.theta.xcfa.utils.memoryTypeKey
import hu.bme.mit.theta.xcfa.utils.references

internal class XcfaToEventGraph(
  private val xcfa: XCFA,
  private val parseContext: ParseContext,
  private val property: ErrorDetection,
  private val pruneCandidates: Boolean = false,
  private val dischargeDeadTargets: Boolean = false,
) {

  init {
    if (xcfa.initProcedures.size > 1) exit("multiple entry points.")
  }

  data class EventGraph(
    val name: String,
    val threads: Set<Thread>,
    val events: Map<VarDecl<*>, Map<Int, List<E>>>,
    val pos: List<R>, // not transitively closed!
    val rfs: Map<VarDecl<*>, Set<R>>,
    val wss: Map<VarDecl<*>, Set<R>>,
    val violations: List<Violation>, // OR!
    val branchingConditions: List<Expr<BoolType>>,
    val localFlows: List<Expr<BoolType>>, // data flow of procedure-local variables (no events)
    val edgeGuards: Map<Pair<Int, XcfaEdge>, Expr<BoolType>>, // path guard after each edge
    val memoryDecls: Set<VarDecl<*>>,
    val memoryGarbages: Set<IndexedConstDecl<*>>,
    val unrollExits: List<UnrollExit>,
  ) {

    override fun toString(): String =
      proceduresToDot(name, threads.map { it.procedure }) { procedureName, edge ->
        val thread = threads.find { it.procedure.name == procedureName }
        " [${
          events.values
            .flatMap {
              if (thread != null) {
                it[thread.pid] ?: listOf()
              } else {
                it.flatMap { e -> e.value }
              }
            }
            .filter { e -> e.pid == (thread?.pid ?: e.pid) && e.edge == edge }
            .joinToString(",") { it.const.name }
        }]"
      }
  }

  private val threads = mutableSetOf<Thread>()
  private var indexing = VarIndexingFactory.indexing(0)
  private val localVars = mutableMapOf<VarDecl<*>, MutableMap<Int, VarDecl<*>>>()

  private val events: MutableMap<VarDecl<*>, MutableMap<Int, MutableList<E>>> = mutableMapOf()
  private val pos: MutableList<R> = mutableListOf()
  private val rfs: MutableMap<VarDecl<*>, MutableSet<R>> = mutableMapOf()
  private var wss = mutableMapOf<VarDecl<*>, MutableSet<R>>()
  private val violations: MutableList<Violation> = mutableListOf()
  private val branchingConditions: MutableList<Expr<BoolType>> = mutableListOf()
  private val localFlows: MutableList<Expr<BoolType>> = mutableListOf()
  private val localDefinitions = mutableMapOf<ConstDecl<*>, MutableList<LocalDefinition>>()
  private val edgeGuards = mutableMapOf<Pair<Int, XcfaEdge>, Expr<BoolType>>()
  private val unrollExits: MutableList<UnrollExit> = mutableListOf()

  /**
   * Per started thread, a global flag its final location sets. A join reads it, so the join is
   * ordered after the thread by that read -- which, unlike a program-order edge, binds only when
   * the join executes. See [addJoinOrders].
   */
  private val doneVars = mutableMapOf<Int, VarDecl<BoolType>>()

  private class PendingJoin(val finals: Set<E>, val join: E)

  private val joins = mutableListOf<PendingJoin>()

  private val createdKeys = mutableSetOf<Expr<*>>()

  private val racingGlobals: Set<VarDecl<*>> =
    xcfa.globalVars.filter { !it.threadLocal && !it.atomic }.map { it.wrappedVar }.toSet()

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

  /**
   * One memory declaration per [MemoryTypeKey], typed with the partition's element type.
   *
   * Partitioning memory declarations by array type, offset type, and expression type as there
   * should never be data flow between events where any of these differ.
   */
  private val memoryDecls: Map<MemoryTypeKey, VarDecl<Type>> = createMemoryDecls()

  /**
   * Thread-specific data: per thread, a partition of slots addressed by `pthread_key_t` values
   * (which `pthread_key_create` makes fresh, see CLibraryFunctionsPass). Not a partition of program
   * memory: a slot used to be the key object's own memory at offset `pid`, which under the flat
   * model is the absolute address `pid` -- some other object.
   */
  private val threadSpecificDecls: Map<Int, VarDecl<Type>> = createThreadSpecificDecls()

  private val memoryDeclSet: Set<VarDecl<*>> =
    memoryDecls.values.toSet() + threadSpecificDecls.values

  /**
   * Declarations for initial memory garbage: the values of these declarations are not constrained
   */
  private val memoryGarbages: Map<VarDecl<Type>, IndexedConstDecl<Type>> =
    (memoryDecls.values + threadSpecificDecls.values)
      .associateWith { it.getNewIndexed() }
      .also { XcfaEvent.memoryGarbages = it.values.toSet() }

  fun create(): EventGraph {
    XcfaEvent.resetIds()
    Thread.resetIds()
    ThreadProcessor(
        Thread.of(
          xcfa.initProcedures.first().first,
          parseContext,
          allocationSites = allocationSites,
        ),
        true,
      )
      .process()
    addCrossThreadRelations()
    addJoinOrders()
    val allEvents = events.values.flatMap { it.values.flatten() }
    val before = closePo(allEvents, pos)
    // RF-Some would make a read take such a candidate, ruling out every execution: a read that no
    // write can precede is simply unconstrained.
    rfs.values.forEach { rels -> rels.removeIf { before[it.from]?.get(it.to.id) == true } }
    if (pruneCandidates) {
      val analysis =
        XcfaOcValueAnalysis(
          allEvents,
          before,
          rfs,
          wss,
          localDefinitions,
          memoryGarbages.values.toSet(),
          parseContext.isCheckMemsafety,
        )
      analysis.prune().forEach { localFlows.add(Not(it.toAnd())) }
      if (dischargeDeadTargets) {
        violations.removeIf { analysis.isCertainlyFalse(it.guard) }
        unrollExits.removeIf { analysis.isCertainlyFalse(it.guard) }
      }
    }
    return EventGraph(
      xcfa.name,
      threads,
      events,
      pos,
      rfs,
      wss,
      violations,
      branchingConditions,
      localFlows,
      edgeGuards,
      memoryDeclSet,
      memoryGarbages.values.toSet(),
      unrollExits,
    )
  }

  /**
   * Collects the partitions occurring in the XCFA and creates a memory declaration for each.
   *
   * Up front rather than lazily: every partition needs an unconstrained initial write that is
   * program-order-before all other events, and such an event can only be created while the entry
   * thread is being set up.
   */
  private fun createMemoryDecls(): Map<MemoryTypeKey, VarDecl<Type>> {
    val keys = mutableSetOf<MemoryTypeKey>()
    xcfa.procedures.forEach { procedure ->
      procedure.edges.forEach { edge ->
        edge.label.dereferences.forEach { keys.add(it.memoryTypeKey) }
      }
    }
    val names = mutableSetOf<String>()
    // sorted so that the generated names do not depend on traversal order
    return keys
      .sortedBy { it.toString() }
      .associateWith { key ->
        var name = "__theta_oc_memory_declaration__${key.sanitizedName}"
        while (!names.add(name)) name += "_" // types with equal sanitized names (should not happen)
        Decls.Var(name, key.elemType)
      }
  }

  private fun createThreadSpecificDecls(): Map<Int, VarDecl<Type>> {
    val labels =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<InvokeLabel>()
    // the slots hold `void *` values: the result of a get, the value of a set
    val types =
      labels
        .mapNotNull {
          when (it.name) {
            "pthread_getspecific" -> it.params[0].type
            "pthread_setspecific" -> it.params[2].type
            else -> null
          }
        }
        .toSet()
    if (types.size > 1) exit("thread-specific values of different types: $types")
    val type = types.singleOrNull() ?: return mapOf()
    return (0 until maxPid).associateWith { Decls.Var("__theta_oc_thread_specific_$it", type) }
  }

  private val Dereference<*, *, *>.memoryDecl: VarDecl<Type>
    get() =
      memoryDecls[memoryTypeKey]
        ?: exit("dereference of an unregistered type: $memoryTypeKey ($this)")

  private fun addCrossThreadRelations() {
    val locals = localVars.values.flatMap { it.values }.toSet()
    for ((v, map) in events) {
      if (map.values.all { it.all { e -> e.assignment == null } })
        exit("variable $v is not initialized")
      // the only cross-thread local accesses are thread parameters, passed in localFlows
      if (v in locals) continue
      for ((pid1, list1) in map) for ((pid2, list2) in map) if (pid1 != pid2)
        for (e1 in list1.filter { it.type == WRITE }) for (e2 in list2) {
          // statically different addresses never alias: no relation between them
          if (!e1.potentialSameMemory(e2)) continue
          if (e2.type == READ) rfs.add(RelationType.RF, e1, e2)
          if (e2.type == WRITE) wss.add(RelationType.WS, e1, e2)
        }
    }
  }

  /**
   * Orders a joined thread's final events before the join only when every event after the join
   * implies that it executed: [pos] is closed statically, so after `if (c) pthread_join(t, 0);` an
   * unconditional order would put the merged path after `t` even when the join did not run. A
   * conditional join is ordered by the read of the thread's done flag instead.
   */
  private fun addJoinOrders() {
    val successors = pos.groupBy({ it.from }, { it.to })
    for ((finals, join) in joins.map { it.finals to it.join }) {
      val seen = mutableSetOf(join)
      val todo = ArrayDeque(listOf(join))
      var unconditional = true
      val implied = join.guard.associateWith { mutableMapOf<Expr<BoolType>, Boolean>() }
      while (unconditional && todo.isNotEmpty()) {
        val e = todo.removeFirst()
        if (!implied.all { (c, memo) -> e.guard.any { it.implies(c, memo) } }) unconditional = false
        successors[e]?.forEach { if (seen.add(it)) todo.add(it) }
      }
      if (unconditional) finals.forEach { po(it, join) }
    }
  }

  /**
   * A structural (incomplete, but sound) check that [this] implies [c]: merges after the join wrap
   * its guard in an `Or` of the branches, each of which still conjoins it.
   */
  private fun Expr<BoolType>.implies(
    c: Expr<BoolType>,
    memo: MutableMap<Expr<BoolType>, Boolean>,
  ): Boolean =
    this == c ||
      memo.getOrPut(this) {
        when (this) {
          is AndExpr -> ops.any { it.implies(c, memo) }
          is OrExpr -> ops.all { it.implies(c, memo) }
          else -> false
        }
      }

  private val allocationSites = AllocationSites(xcfa, parseContext)

  private inner class ThreadProcessor(
    private val thread: Thread,
    addMemoryGarbage: Boolean = false,
    private val initialLocalValues: Map<VarDecl<*>, IndexedConstDecl<*>> = mapOf(),
  ) {

    private val pid = thread.pid
    private var last = listOf<E>()
    private var guard = setOf<Expr<BoolType>>()
    private lateinit var lastWrites: MutableMap<VarDecl<*>, Set<E>>

    // SSA value of each thread-local variable: local reads are bound to it instead of rf edges
    private lateinit var localValues: MutableMap<VarDecl<*>, IndexedConstDecl<*>>
    private val memoryWrites = mutableMapOf<VarDecl<*>, MutableSet<E>>()

    /** A thread-specific slot access being processed, and the partition it belongs to. */
    private var threadSpecificSlot: Pair<Dereference<*, *, *>, VarDecl<Type>>? = null
    private lateinit var edge: XcfaEdge
    private var inEdge = false
    private var atomicBlock: Int? = null
    private val multipleUsePidVars = mutableSetOf<VarDecl<*>>()

    // accesses synthesised for a library call are not program accesses: they do not race
    private var inLibraryCall = false

    init {
      if (addMemoryGarbage) {
        val firstEdge = thread.procedure.initLoc.outgoingEdges.first()
        last =
          memoryGarbages.map { (decl, garbage) ->
            val e = E(garbage, WRITE, setOf(), pid, firstEdge, E.uniqueClkId())
            e.assignment = True()
            memoryWrites.getOrPut(decl) { mutableSetOf() }.add(e)
            events.getOrPut(decl) { mutableMapOf() }.getOrPut(thread.pid) { mutableListOf() }.add(e)
            e
          }
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
      e.inAtomicBlock = atomicBlock != null
      e.raceCandidate = property == DATA_RACE && !inLibraryCall && d in racingGlobals
      last.forEach { po(it, e) }
      inEdge = true
      val local = decl != d
      when (type) {
        READ ->
          if (local) {
            localValues[decl]?.let { localFlows.add(Imply(e.guardExpr, Eq(e.const.ref, it.ref))) }
          } else {
            lastWrites[decl]?.forEach { rfs.add(RelationType.RF, it, e) }
          }
        WRITE -> {
          lastWrites[decl] = setOf(e)
          if (local) localValues[decl] = e.const
        }
      }
      events.getOrPut(decl) { mutableMapOf() }.getOrPut(pid) { mutableListOf() }.add(e)
      return listOf(e)
    }

    /**
     * Procedure-local variables (each thread's own copy) have no events: a read is the variable's
     * current SSA value, a write a fresh constant bound to the written value under the path guard.
     * Thread handles keep their events in [StartLabel] / [JoinLabel], which order the threads.
     */
    private fun VarDecl<*>.isLocal(varPid: Int = pid) = threadVar(varPid) != this

    private fun localRead(d: VarDecl<*>): IndexedConstDecl<*> {
      val decl = d.threadVar(pid)
      // an unwritten local has some (unconstrained) value, the same at every read
      return localValues.getOrPut(decl) { decl.getNewIndexed() }
    }

    private fun localWrite(d: VarDecl<*>, value: Expr<*>?, varPid: Int = pid) {
      val decl = d.threadVar(varPid)
      val const = decl.getNewIndexed()
      if (value != null) localFlows.add(underGuard(Eq(const.ref, value)))
      localDefinitions.getOrPut(const) { mutableListOf() }.add(LocalDefinition(guard, value))
      localValues[decl] = const
    }

    private fun underGuard(e: Expr<BoolType>): Expr<BoolType> =
      if (guard.isEmpty()) e else Imply(guard.toAnd(), e)

    private fun memoryEvent(
      deref: Dereference<*, *, *>,
      consts: Map<Any, IndexedConstDecl<*>>,
      type: EventType,
      useProvidedConst: Boolean = false,
    ): List<E> {
      check(!inEdge || last.size == 1)
      val decl =
        threadSpecificSlot?.takeIf { (slot, _) -> slot === deref }?.second ?: deref.memoryDecl
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
          decl.getNewIndexed()
        }
      val e = E(const, type, guard, pid, edge, clkId, array, offset)
      e.inAtomicBlock = atomicBlock != null
      e.raceCandidate =
        property == DATA_RACE &&
          !inLibraryCall &&
          // an address that cannot be resolved is not known to be atomic: keep it as a candidate
          runCatching { !deref.addressesAtomicData(xcfa.globalVars, parseContext) }
            .getOrDefault(true)
      last.forEach { po(it, e) }
      inEdge = true
      when (type) {
        // only same-partition writes can be observed (see MemoryTypeKey)
        READ ->
          memoryWrites[decl]?.forEach {
            if (it.potentialSameMemory(e)) rfs.add(RelationType.RF, it, e)
          }
        WRITE -> memoryWrites.getOrPut(decl) { mutableSetOf() }.add(e)
      }
      events.getOrPut(decl) { mutableMapOf() }.getOrPut(pid) { mutableListOf() }.add(e)
      return listOf(e)
    }

    private fun <T : Type> Expr<T>.toEvents(
      consts: Map<Any, IndexedConstDecl<*>>? = null,
      useProvidedConst: Boolean = false,
    ): Map<Any, IndexedConstDecl<*>> {
      val mutConsts = consts?.toMutableMap() ?: mutableMapOf()
      vars.forEach {
        if (it.isLocal()) {
          if (!useProvidedConst) mutConsts[it] = localRead(it)
        } else {
          last = event(it, READ)
          if (!useProvidedConst) mutConsts[it] = last.first().const
        }
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
            localValues.add(initialLocalValues)
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
          current.atomics.all { it == current.atomics.first() } || current.loc.isTerminalSink()
        ) {
          "incoming paths disagree on atomic nesting at ${current.loc.name}: ${current.atomics}"
        }

        if (current.loc.error) {
          val errorGuard = Or(current.guards.map { it.toAnd() })
          violations.add(Violation(current.loc, pid, errorGuard, current.lastEvents))
          continue
        }

        UnrollCut.keyOf(current.loc)?.let { key ->
          unrollExits.add(UnrollExit(key, pid, Or(current.guards.map { it.toAnd() })))
          continue
        }

        if (current.loc.final) {
          val doneEdge = current.loc.incomingEdges.firstOrNull()
          if (thread.pidVar != null && doneEdge != null) {
            val done = doneVars.getOrPut(pid) { Decls.Var("__theta_oc_thread_done_$pid", Bool()) }
            edge = doneEdge
            inEdge = false
            atomicBlock = current.atomics.firstOrNull()
            last = current.lastEvents
            guard = current.guards.toOrInSet()
            lastWrites = current.lastWrites.merge().toMutableMap()
            val write = event(done, WRITE).first()
            write.assignment = True()
            thread.finalEvents.add(write)
          } else {
            thread.finalEvents.addAll(current.lastEvents)
          }
        }

        val mergedGuard = current.guards.toOrInSet()
        val mergedLocalValues = mergeLocalValues(current)
        val assumeConsts = mutableMapOf<Any, MutableList<ConstDecl<*>>>()

        for (e in current.loc.outgoingEdges) {
          edge = e
          inEdge = false
          last = current.lastEvents
          // intersection of guards of incoming edges:
          guard = mergedGuard
          lastWrites = current.lastWrites.merge().toMutableMap()
          localValues = mergedLocalValues.toMutableMap()
          val threadLookup =
            current.threadLookups
              .merge { s1, s2 ->
                s1 + s2.filter { (guard2, _) -> s1.none { (guard1, _) -> guard1 == guard2 } }
              }
              .toMutableMap()
          var firstLabel = true
          var leadingAssume = true
          atomicBlock = current.atomics.firstOrNull()

          edge.getFlatLabels().forEach { label ->
            if (label.references.isNotEmpty()) exit("references")
            leadingAssume = leadingAssume && label is StmtLabel && label.stmt is AssumeStmt
            when (label) {
              is StmtLabel -> {
                when (val stmt = label.stmt) {
                  is AssignStmt<*> -> stmt.process()
                  is AssumeStmt -> stmt.process(assumeConsts, firstLabel, leadingAssume)
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

          edgeGuards[pid to edge] = guard.toAnd()

          val searchItem =
            waitList.find { it.loc == edge.target }
              ?: SearchItem(edge.target).apply { waitList.add(this) }
          searchItem.guards.add(guard)
          searchItem.lastEvents.addAll(last)
          searchItem.lastWrites.add(lastWrites)
          searchItem.localValues.add(localValues)
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
            val labels = e.getFlatLabels()
            // A label-less edge is semantically assume(true): it contributes no condition, so the
            // guard simply carries over unchanged, which is what the loop above already did. Only a
            // branch that *starts with something other than a condition* is unsupported.
            if (labels.isEmpty()) continue
            val first = labels.first()
            if (first !is StmtLabel || first.stmt !is AssumeStmt) {
              exit("branching with non-assume labels (${first::class.simpleName}: $first)")
            }
          }
          assumeConsts.forEach { (_, set) ->
            for ((i1, v1) in set.withIndex()) for ((i2, v2) in set.withIndex()) {
              if (i1 == i2) break
              // the constants in the different branches must be equal
              if (v1 != v2) branchingConditions.add(Eq(v1.ref, v2.ref))
            }
          }
        }
      }

      if (waitList.isNotEmpty())
        exit(
          "loops and dangling edges (stuck at ${waitList.joinToString(", ", limit = 5) { item ->
            "${item.loc.name}[${item.incoming}/${item.loc.incomingEdges.size}]"
          }})"
        )
    }

    /**
     * Merges the local values reaching [current] from its incoming paths: a variable whose value
     * differs between them gets a fresh constant equal to its value on the path taken (left
     * unconstrained by a path on which it is unassigned).
     */
    private fun mergeLocalValues(current: SearchItem): Map<VarDecl<*>, IndexedConstDecl<*>> {
      val incoming = current.localValues
      if (incoming.size <= 1) return incoming.firstOrNull() ?: mapOf()
      check(incoming.size == current.guards.size)
      val merged = mutableMapOf<VarDecl<*>, IndexedConstDecl<*>>()
      for (v in incoming.flatMap { it.keys }.toSet()) {
        val values = incoming.map { it[v] }
        val first = values.first()
        if (first != null && values.all { it == first }) {
          merged[v] = first
          continue
        }
        val phi = v.getNewIndexed()
        localDefinitions[phi] =
          current.guards
            .zip(values)
            .map { (g, value) -> LocalDefinition(g, value?.ref) }
            .toMutableList()
        val options =
          current.guards.zip(values).map { (g, value) ->
            if (value == null) g.toAnd() else And(g.toAnd(), Eq(phi.ref, value.ref))
          }
        localFlows.add(Imply(current.guards.toOrInSet().toAnd(), Or(options)))
        merged[v] = phi
      }
      return merged
    }

    /**
     * A location an execution cannot leave except into the error location, or cannot leave at all.
     *
     * Inlining copies a callee's error location as an ordinary one -- `inlinedCopy` clears the
     * `error` flag -- and joins it to the caller's error location with a do-nothing edge; nested
     * inlining chains several of those together, so only the last link carries the flag. Paths
     * reaching such a sink may legitimately disagree about atomic nesting, because execution stops
     * there either way, so the agreement check has to see through the whole chain rather than one
     * link. (The joining edge carries `SequenceLabel(listOf(NopLabel))`, which `getFlatLabels`
     * keeps rather than drops, so testing for an empty label does not recognise it either.)
     */
    private fun XcfaLocation.isTerminalSink(
      seen: MutableSet<XcfaLocation> = mutableSetOf()
    ): Boolean {
      if (error) return true
      // Execution stops here, so there is no later event for an atomic context to govern and the
      // incoming paths need not agree on one. A thread's final location legitimately collects both
      // ordinary completion and, once MemsafetyPass has redirected the error edges into it
      // (breakUpErrors), paths that were inside a locked region -- which is where the overwhelming
      // majority of the memsafety runs were failing.
      if (final || outgoingEdges.isEmpty()) return true
      if (!seen.add(this)) return false
      val edge = outgoingEdges.singleOrNull() ?: return false
      val doesNothing = { l: XcfaLabel -> l is NopLabel || (l is StmtLabel && l.stmt is SkipStmt) }
      return edge.label.getFlatLabels().all(doesNothing) && edge.target.isTerminalSink(seen)
    }

    private fun AssignStmt<*>.process() {
      val consts = this.expr.toEvents()
      if (varDecl.isLocal()) {
        localWrite(varDecl, this.expr.with(consts))
        return
      }
      last = event(this.varDecl, WRITE)
      last.first().assignment = Eq(last.first().const.ref, this.expr.with(consts))
    }

    private fun AssumeStmt.process(
      assumeConsts: MutableMap<Any, MutableList<ConstDecl<*>>>,
      firstLabel: Boolean,
      leadingAssume: Boolean,
    ) {
      val consts =
        this.cond.vars.associateWith {
          if (it.isLocal()) localRead(it) else it.threadVar(pid).getNewIndexed(false)
        } + this.cond.dereferences.associateWith { it.memoryDecl.getNewIndexed(true) }
      val condWithConsts = this.cond.with(consts)
      val asAssign =
        consts.size == 1 &&
          consts.keys.first().let { c ->
            c is VarDecl<*> &&
              !c.isLocal() &&
              c.threadVar(pid).let { v ->
                v !in lastWrites ||
                  lastWrites[v]?.let { it.size == 1 && it.first().assignment == True() } == true
              }
          }

      val outgoingEdgesSize = edge.source.outgoingEdges.size
      if (outgoingEdgesSize > 1 || !asAssign) {
        guard = guard + condWithConsts
        // a branch condition can follow other assumes (e.g. a null check): it still reads the value
        // the other branch reads, or both branches could be taken at once
        if (leadingAssume) {
          consts.forEach { (v, c) -> assumeConsts.getOrPut(v) { mutableListOf() }.add(c) }
        }
      }
      this.cond.toEvents(consts, true)
      if ((outgoingEdgesSize == 1 || !firstLabel) && asAssign) {
        last.first().assignment = condWithConsts
      }
    }

    private fun HavocStmt<*>.process() {
      if (varDecl.isLocal()) {
        localWrite(varDecl, null)
        return
      }
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

      // assign parameters
      procedure.params.forEachIndexed { index, param ->
        if (param.second != ParamDirection.OUT) {
          val consts = this.params[index].toEvents()
          localWrite(param.first, this.params[index].with(consts), newPid)
        }
      }

      last = event(this.pidVar, WRITE)
      val pidVar = this.pidVar.threadVar(pid)
      if (threads.any { it.pidVar == pidVar }) {
        multipleUsePidVars.add(pidVar)
      }
      val newHistory = thread.startHistory + thread.procedure.name
      val newThread =
        Thread.of(
          procedure,
          parseContext,
          params,
          newPid,
          guard,
          pidVar,
          last.first(),
          newHistory,
          lastWrites,
          allocationSites,
        )
      // a literal of the handle's own type: Eq(bv, Int) would cast the handle to Int, which some
      // solvers (e.g. Yices) do not support
      val handle = last.first().const
      last.first().assignment = Eq(handle.ref, handle.type.integerOf(newPid))
      threadLookup[pidVar] = setOf(Pair(guard, newThread))
      // the parameters written above are locals of the new thread
      ThreadProcessor(newThread, initialLocalValues = localValues.toMap()).process()
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
        doneVars[thread.pid]?.let { done ->
          val incoming = last
          last = listOf(joinEvent)
          event(done, READ)
          last = incoming
        }
        joins.add(PendingJoin(thread.finalEvents.toSet(), joinEvent))
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
      // a block begun mid-edge continues the edge's atomic unit
      if (this is AtomicBeginLabel) {
        atomicBlock = if (inEdge) last.first().clkId else E.uniqueClkId()
      }
      if (this is AtomicEndLabel) atomicBlock = null
    }

    /** The pthread functions' `int` result: 0, as they do not fail. */
    private fun <T : Type> VarDecl<T>.assignZero() = Assign(this, type.integerOf(0)).process()

    /** Processes [access] of the slot of [key] in thread [slotPid]. */
    private fun threadSpecific(
      key: Expr<*>,
      slotPid: Int,
      access: (Dereference<*, *, Type>) -> Unit,
    ) {
      val decl = threadSpecificDecls[slotPid] ?: exit("no thread-specific slot for thread $slotPid")
      val slot = Dereference.of(cast(key, key.type), Int(0), decl.type)
      threadSpecificSlot = slot to decl
      try {
        access(slot)
      } finally {
        threadSpecificSlot = null
      }
    }

    private fun InvokeLabel.process() {
      inLibraryCall = true
      try {
        processLibraryCall()
      } finally {
        inLibraryCall = false
      }
    }

    private fun InvokeLabel.processLibraryCall() {
      when (name) {
        "pthread_getspecific" -> {
          val ret = (params[0] as RefExpr<*>).decl as VarDecl<*>
          threadSpecific(params[1], pid) { slot -> Assign(cast(ret, slot.type), slot).process() }
        }

        "pthread_setspecific" -> {
          val ret = (params[0] as RefExpr<*>).decl as VarDecl<*>
          threadSpecific(params[1], pid) { slot ->
            MemoryAssignStmt.of(slot, cast(params[2], slot.type)).process()
          }
          ret.assignZero()
        }

        "pthread_key_create" -> {
          val isNull = Eq(params[2], params[2].type.integerOf(0))
          if (ExprSimplifier.create().simplify(isNull, ImmutableValuation.empty()) != True()) {
            exit("pthread_key_create with non-null destructor")
          }
          // the key is fresh per call site (CLibraryFunctionsPass): executing it twice would
          // reuse it, and the two keys would share their slots
          if (!createdKeys.add(params[1])) exit("pthread_key_create executed more than once")
          val ret = (params[0] as RefExpr<*>).decl as VarDecl<*>
          threadSpecificDecls.keys.forEach { i ->
            threadSpecific(params[1], i) { slot ->
              MemoryAssignStmt.of(slot, slot.type.integerOf(0)).process()
            }
          }
          ret.assignZero()
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
    if (
      this !in memoryDeclSet &&
        doneVars.values.none { it == this } &&
        xcfa.globalVars.none { it.wrappedVar == this && !it.threadLocal }
    ) {
      // if not global var
      cast(
        localVars
          .getOrPut(this) { mutableMapOf() }
          .getOrPut(pid) { Decls.Var("t$pid::$name", type) },
        type,
      )
    } else this

  private fun exit(msg: String): Nothing {
    error("Feature not supported by OC checker: $msg.")
  }
}
