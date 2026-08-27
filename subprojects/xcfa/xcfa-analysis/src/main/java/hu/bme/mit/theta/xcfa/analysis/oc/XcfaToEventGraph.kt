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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprSimplifier
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.references

internal class XcfaToEventGraph(private val xcfa: XCFA, private val parseContext: ParseContext) {

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
    val memoryDecls: Set<VarDecl<*>>,
    val memoryGarbages: Set<IndexedConstDecl<*>>,
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

  /**
   * Identifies a *memory partition*: the set of dereferences sharing an (array, offset, element)
   * type triple.
   *
   * A single, [IntType]-typed memory declaration cannot represent the value of every dereference:
   * the const standing for a memory event is substituted back into the surrounding expression (see
   * [with]), where it must have the dereference's real element type. Bitvector-typed accesses (a C
   * program analysed with bitvector arithmetic) therefore failed with a `ClassCastException`, and
   * there is no expression converting an `Int` const back to a `Bv` (only `Bv -> Int` exists), so
   * the value has to be tracked at the accessed type in the first place.
   *
   * This is exactly the partitioning the rest of Theta's memory model uses:
   * `DereferenceToArrayPass` allocates one backing array (`__arrays_<A>_<O>_<T>`) per such triple,
   * so accesses of different types never communicate there either. Keeping the OC encoding in sync
   * means the OC backend makes the same aliasing assumptions as the CEGAR backends rather than
   * inventing new ones.
   *
   * Note that the partitioning cannot hide a data race: races are detected by the instrumentation
   * of `DataRaceToReachabilityPass` (ordinary flag variables holding the racing address), not by
   * the read-from relation. Splitting only removes read-from edges, and since every partition keeps
   * its own unconstrained "garbage" initial write, a read that loses a cross-type source falls back
   * to an arbitrary value -- i.e. the encoding gains behaviours, never loses them.
   */
  private data class MemoryKey(val arrayType: Type, val offsetType: Type, val elemType: Type)

  private val Dereference<*, *, *>.memoryKey: MemoryKey
    get() = MemoryKey(array.type, offset.type, type)

  /** One memory declaration per partition, typed with the partition's element type. */
  private val memoryDecls: Map<MemoryKey, VarDecl<Type>> = createMemoryDecls()
  private val memoryDeclSet: Set<VarDecl<*>> = memoryDecls.values.toSet()

  // the values of these declarations are not constrained
  private val memoryGarbages: Map<MemoryKey, IndexedConstDecl<Type>> =
    memoryDecls
      .mapValues { (_, decl) -> decl.getNewIndexed() }
      .also { XcfaEvent.memoryGarbages = it.values.toSet() }

  fun create(): EventGraph {
    ThreadProcessor(Thread.of(xcfa.initProcedures.first().first, parseContext), true).process()
    addCrossThreadRelations()
    return EventGraph(
      xcfa.name,
      threads,
      events,
      pos,
      rfs,
      wss,
      violations,
      branchingConditions,
      memoryDeclSet,
      memoryGarbages.values.toSet(),
    )
  }

  /**
   * Collects every dereference type triple occurring in the XCFA and creates a memory declaration
   * for each.
   *
   * This has to happen up front (rather than lazily, on first access): every partition needs an
   * unconstrained initial write that is program-order-before all other events, and such an event
   * can only be created while the entry thread is being set up. A read with no read-from source at
   * all would be left with a completely free value, which would be unsound.
   */
  private fun createMemoryDecls(): Map<MemoryKey, VarDecl<Type>> {
    val keys = mutableSetOf<MemoryKey>()
    xcfa.procedures.forEach { procedure ->
      procedure.edges.forEach { edge ->
        edge.label.dereferences.forEach { keys.add(it.memoryKey) }
        edge.getFlatLabels().filterIsInstance<InvokeLabel>().forEach { label ->
          pthreadSpecificKey(label)?.let { keys.add(it) }
        }
      }
    }
    val names = mutableSetOf<String>()
    // sorted so that the generated names do not depend on traversal order
    return keys
      .sortedBy { it.toString() }
      .associateWith { key ->
        var name = "__oc_memory_declaration__${key.suffix}"
        while (!names.add(name)) name += "_" // types with equal sanitized names (should not happen)
        Decls.Var(name, key.elemType)
      }
  }

  /**
   * `pthread_{get,set}specific` and `pthread_key_create` are modelled with dereferences synthesised
   * in [ThreadProcessor.process] that are not present in the XCFA itself, so their partitions have
   * to be registered separately.
   */
  private fun pthreadSpecificKey(label: InvokeLabel): MemoryKey? {
    val keyType =
      when (label.name) {
        "pthread_getspecific",
        "pthread_setspecific" -> (label.params.getOrNull(1) as? Dereference<*, *, *>)?.array?.type

        "pthread_key_create" ->
          ((label.params.getOrNull(1) as? RefExpr<*>)?.decl as? VarDecl<*>)?.type

        else -> null
      } ?: return null
    return MemoryKey(keyType, Int(), Int())
  }

  /** Alphanumeric rendering of the triple (const names must stay parseable, see reason parser) */
  private val MemoryKey.suffix: String
    get() =
      listOf(arrayType, offsetType, elemType).joinToString("_") {
        it.toString().replace(Regex("[^A-Za-z0-9]"), "")
      }

  private fun memoryDeclOf(deref: Dereference<*, *, *>): VarDecl<Type> =
    memoryDecls[deref.memoryKey]
      ?: exit("dereference of an unregistered type: ${deref.memoryKey} ($deref)")

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
    private val memoryWrites = mutableMapOf<MemoryKey, MutableSet<E>>()
    private lateinit var edge: XcfaEdge
    private var inEdge = false
    private var atomicBlock: Int? = null
    private val multipleUsePidVars = mutableSetOf<VarDecl<*>>()

    init {
      if (addMemoryGarbage) {
        val firstEdge = thread.procedure.initLoc.outgoingEdges.first()
        last =
          memoryGarbages.map { (key, garbage) ->
            val e = E(garbage, WRITE, setOf(), pid, firstEdge, E.uniqueClkId())
            e.assignment = True()
            memoryWrites.getOrPut(key) { mutableSetOf() }.add(e)
            events
              .getOrPut(memoryDecls.getValue(key)) { mutableMapOf() }
              .getOrPut(thread.pid) { mutableListOf() }
              .add(e)
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
      val key = deref.memoryKey
      val decl = memoryDeclOf(deref)
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
      last.forEach { po(it, e) }
      inEdge = true
      when (type) {
        // only same-partition writes can be observed (see MemoryKey)
        READ -> memoryWrites[key]?.forEach { rfs.add(RelationType.RF, it, e) }
        WRITE -> memoryWrites.getOrPut(key) { mutableSetOf() }.add(e)
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
      val visited = mutableSetOf<XcfaLocation>()
      /**
       * Items let through with fewer incoming edges than the location has, because the missing ones
       * can never fire (see [releasableFrom]); their per-edge collections are correspondingly
       * shorter, so the arity checks below must not demand the full count for them.
       */
      val releasedEarly = mutableSetOf<SearchItem>()
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
        visited.add(current.loc)
        check(current.incoming == current.loc.incomingEdges.size || current in releasedEarly)
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
              branchingConditions.add(Eq(v1.ref, v2.ref))
            }
          }
        }

        // The frontier can drain with items still waiting, because loop unrolling leaves behind
        // copies past the unroll bound that nothing can reach. An edge out of such a location can
        // never fire, so waiting for it would strand a perfectly ordinary merge point forever --
        // that is the "dangling edges" half of the old error. Let those items through with the
        // predecessors they did get. A real loop is unaffected: its head is blocked by its own
        // back edge, whose source is reachable from the head itself, so it is never releasable and
        // still reports below.
        if (toVisit.isEmpty() && waitList.isNotEmpty()) {
          val releasable = releasableFrom(waitList, visited)
          if (releasable.isEmpty()) {
            if (System.getenv("THETA_OC_LOOP_DEBUG") != null) {
              System.err.println("=== OC loop stall: ${waitList.size} waiting item(s)")
              val fromInit = mutableSetOf(thread.procedure.initLoc)
              val q = mutableListOf(thread.procedure.initLoc)
              while (q.isNotEmpty()) q.removeLast().outgoingEdges.forEach {
                if (fromInit.add(it.target)) q.add(it.target)
              }
              waitList.forEach { item ->
                val downstream = mutableSetOf(item.loc)
                val q2 = mutableListOf(item.loc)
                while (q2.isNotEmpty()) q2.removeLast().outgoingEdges.forEach {
                  if (downstream.add(it.target)) q2.add(it.target)
                }
                val missing = item.loc.incomingEdges.filter { it.source !in visited }
                System.err.println(
                  "  ${item.loc.name}[${item.incoming}/${item.loc.incomingEdges.size}]" +
                    " missing-from=" +
                    missing.joinToString(",", limit = 8) { e ->
                      val reachInit = if (e.source in fromInit) "reachable" else "DEAD"
                      val cyc = if (e.source in downstream) "CYCLE" else "acyclic"
                      "${e.source.name}($reachInit,$cyc)"
                    }
                )
              }
            }
            exit(
              "loops (stuck at ${waitList.joinToString(", ", limit = 5) { item ->
                "${item.loc.name}[${item.incoming}/${item.loc.incomingEdges.size}]"
              }})"
            )
          }
          releasedEarly.addAll(releasable)
          waitList.removeAll(releasable)
          toVisit.addAll(releasable)
        }
      }
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
      return edge.label.getFlatLabels().all { it is NopLabel } && edge.target.isTerminalSink(seen)
    }

    /**
     * The waiting items whose still-missing incoming edges can never be delivered: no location that
     * an execution could still get to (a waiting location, or anything downstream of one) is their
     * source. Returns an empty set when every waiting item is blocked by something still live --
     * i.e. when the blockage is a genuine cycle.
     */
    private fun releasableFrom(
      waitList: Set<SearchItem>,
      visited: Set<XcfaLocation>,
    ): Set<SearchItem> {
      val stillLive = mutableSetOf<XcfaLocation>()
      val stack = waitList.mapTo(mutableListOf()) { it.loc }
      stillLive.addAll(stack)
      while (stack.isNotEmpty()) {
        stack.removeLast().outgoingEdges.forEach {
          if (stillLive.add(it.target)) stack.add(it.target)
        }
      }
      return waitList.filterTo(mutableSetOf()) { item ->
        item.loc.incomingEdges.none { it.source !in visited && it.source in stillLive }
      }
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
          this.cond.dereferences.associateWith { memoryDeclOf(it).getNewIndexed(true) }
      val condWithConsts = this.cond.with(consts)
      val asAssign =
        consts.size == 1 &&
          consts.keys.first().let { c ->
            c is VarDecl<*> &&
              c.threadVar(pid).let { v ->
                v !in lastWrites ||
                  lastWrites[v]?.let { it.size == 1 && it.first().assignment == True() } == true
              }
          }

      val outgoingEdgesSize = edge.source.outgoingEdges.size
      if (outgoingEdgesSize > 1 || !asAssign) {
        guard = guard + condWithConsts
        if (firstLabel) {
          consts.forEach { (v, c) -> assumeConsts.getOrPut(v) { mutableListOf() }.add(c) }
        }
      }
      this.cond.toEvents(consts, true)
      if ((outgoingEdgesSize == 1 || !firstLabel) && asAssign) {
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

      // assign parameters
      procedure.params.forEachIndexed { index, param ->
        if (param.second != ParamDirection.OUT) {
          val consts = this.params[index].toEvents()
          last = event(param.first, WRITE, newPid)
          val e = last.first()
          e.assignment = Eq(e.const.ref, this.params[index].with(consts))
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
        )
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
    if (
      this !in memoryDeclSet && xcfa.globalVars.none { it.wrappedVar == this && !it.threadLocal }
    ) {
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
