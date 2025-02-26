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

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.algorithm.oc.Relation
import hu.bme.mit.theta.analysis.algorithm.oc.RelationType
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.oc.XcfaOcMemoryConsistencyModel.SC
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.*
import kotlin.time.measureTime

private val Expr<*>.vars
  get() = ExprUtils.getVars(this)

class XcfaOcChecker(
  xcfa: XCFA,
  decisionProcedure: OcDecisionProcedureType,
  private val logger: Logger,
  conflictInput: String?,
  private val outputConflictClauses: Boolean,
  nonPermissiveValidation: Boolean,
  autoConflictConfig: AutoConflictFinderConfig,
  autoConflictBound: Int,
  private val memoryModel: XcfaOcMemoryConsistencyModel = SC,
  private val acceptUnreliableSafe: Boolean = false,
) : SafetyChecker<EmptyProof, Cex, XcfaPrec<UnitPrec>> {

  private val xcfa = xcfa.optimizeFurther(OcExtraPasses())
  private val autoConflictFinder = autoConflictConfig.conflictFinder(autoConflictBound)

  private var indexing = VarIndexingFactory.indexing(0)
  private val localVars = mutableMapOf<VarDecl<*>, MutableMap<Int, VarDecl<*>>>()
  private val memoryDecl = Decls.Var("__oc_checker_memory_declaration__", Int())

  private val threads = mutableSetOf<Thread>()
  private val events = mutableMapOf<VarDecl<*>, MutableMap<Int, MutableList<E>>>()
  private val violations = mutableListOf<Violation>() // OR!
  private val branchingConditions = mutableListOf<Expr<BoolType>>()
  private val pos = mutableListOf<R>() // not transitively closed!
  private val rfs = mutableMapOf<VarDecl<*>, MutableSet<R>>()
  private var wss = mutableMapOf<VarDecl<*>, MutableSet<R>>()

  private val ocChecker: OcChecker<E> =
    if (conflictInput == null) decisionProcedure.checker()
    else
      XcfaOcCorrectnessValidator(
        decisionProcedure,
        conflictInput,
        threads,
        !nonPermissiveValidation,
        logger,
      )

  override fun check(prec: XcfaPrec<UnitPrec>?): SafetyResult<EmptyProof, Cex> =
    let {
        if (xcfa.initProcedures.size > 1) exit("multiple entry points")

        logger.mainStep("Adding constraints...")
        xcfa.initProcedures.forEach { ThreadProcessor(Thread(procedure = it.first)).process() }
        addCrossThreadRelations()
        if (!addToSolver(ocChecker.solver)) return@let SafetyResult.safe(EmptyProof.getInstance())

        // "Manually" add some conflicts
        logger.info(
          "Auto conflict time (ms): " +
            measureTime {
                val conflicts = autoConflictFinder.findConflicts(threads, events, rfs, logger)
                ocChecker.solver.add(conflicts.map { Not(it.expr) })
                logger.info("Auto conflicts: ${conflicts.size}")
              }
              .inWholeMilliseconds
        )

        logger.mainStep("Start checking...")
        val status: SolverStatus?
        val (preservedPos, preservedWss) = memoryModel.filter(events, pos, wss)
        val checkerTime = measureTime {
          status = ocChecker.check(events, pos, preservedPos, rfs, preservedWss, memoryModel == SC)
        }
        if (ocChecker !is XcfaOcCorrectnessValidator)
          logger.info("Solver time (ms): ${checkerTime.inWholeMilliseconds}")
        logger.info("Propagated clauses: ${ocChecker.getPropagatedClauses().size}")

        ocChecker.solver.statistics.let {
          logger.info("Solver statistics:")
          it.forEach { (k, v) -> logger.info("$k: $v") }
        }
        when {
          status?.isUnsat == true -> {
            if (outputConflictClauses)
              System.err.println(
                "Conflict clause output time (ms): ${
                        measureTime {
                            ocChecker.getPropagatedClauses().forEach { System.err.println("CC: $it") }
                        }.inWholeMilliseconds
                    }"
              )
            SafetyResult.safe(EmptyProof.getInstance())
          }

          status?.isSat == true -> {
            if (ocChecker is XcfaOcCorrectnessValidator)
              return SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
            if (memoryModel == SC) {
              val trace =
                XcfaOcTraceExtractor(xcfa, ocChecker, threads, events, violations, pos).trace
              SafetyResult.unsafe<EmptyProof, Cex>(trace, EmptyProof.getInstance())
            } else {
              SafetyResult.unsafe<EmptyProof, Cex>(EmptyCex.getInstance(), EmptyProof.getInstance())
            }
          }

          else -> SafetyResult.unknown()
        }
      }
      .also {
        logger.mainStep("OC checker result: $it")
        if (it.isSafe && xcfa.unsafeUnrollUsed && !acceptUnreliableSafe) {
          logger.mainStep("Incomplete loop unroll used: safe result is unreliable.")
          logger.result(SafetyResult.unknown<EmptyProof, Cex>().toString())
          throw NotSolvableException()
        }
      }

  private inner class ThreadProcessor(private val thread: Thread) {

    private val pid = thread.pid
    private var last = listOf<E>()
    private var guard = setOf<Expr<BoolType>>()
    private lateinit var lastWrites: MutableMap<VarDecl<*>, Set<E>>
    private val memoryWrites = mutableSetOf<E>()
    private lateinit var edge: XcfaEdge
    private var inEdge = false
    private var atomicEntered: Boolean? = null
    private val multipleUsePidVars = mutableSetOf<VarDecl<*>>()

    fun event(d: VarDecl<*>, type: EventType, varPid: Int? = null): List<E> {
      check(!inEdge || last.size == 1)
      val decl = d.threadVar(varPid ?: pid)
      val useLastClk = inEdge || atomicEntered == true
      val e =
        if (useLastClk) E(decl.getNewIndexed(), type, guard, pid, edge, last.first().clkId)
        else E(decl.getNewIndexed(), type, guard, pid, edge)
      last.forEach { po(it, e) }
      inEdge = true
      if (atomicEntered == false) atomicEntered = true
      when (type) {
        EventType.READ -> lastWrites[decl]?.forEach { rfs.add(RelationType.RF, it, e) }
        EventType.WRITE -> lastWrites[decl] = setOf(e)
      }
      events.getOrPut(decl) { mutableMapOf() }.getOrPut(pid) { mutableListOf() }.add(e)
      return listOf(e)
    }

    fun memoryEvent(
      deref: Dereference<*, *, *>,
      consts: Map<Any, ConstDecl<*>>,
      type: EventType,
    ): List<E> {
      check(!inEdge || last.size == 1)
      val array = deref.array.with(consts)
      val offset = deref.offset.with(consts)
      val useLastClk = inEdge || atomicEntered == true
      val e =
        if (useLastClk)
          E(memoryDecl.getNewIndexed(), type, guard, pid, edge, last.first().clkId, array, offset)
        else E(memoryDecl.getNewIndexed(), type, guard, pid, edge, array = array, offset = offset)
      last.forEach { po(it, e) }
      inEdge = true
      if (atomicEntered == false) atomicEntered = true
      when (type) {
        EventType.READ -> memoryWrites.forEach { rfs.add(RelationType.RF, it, e) }
        EventType.WRITE -> memoryWrites.add(e)
      }
      events.getOrPut(memoryDecl) { mutableMapOf() }.getOrPut(pid) { mutableListOf() }.add(e)
      return listOf(e)
    }

    fun <T : Type> Expr<T>.toEvents(
      consts: Map<Any, ConstDecl<*>>? = null,
      update: Boolean = true,
    ): Map<Any, ConstDecl<*>> {
      val mutConsts = consts?.toMutableMap() ?: mutableMapOf()
      vars.forEach {
        last = event(it, EventType.READ)
        if (update) mutConsts[it] = last.first().const
      }
      dereferences.forEach {
        last = memoryEvent(it, mutConsts, EventType.READ)
        if (update) mutConsts[it] = last.first().const
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
          val errorGuard = Or(current.lastEvents.map { it.guard.toAnd() })
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
          atomicEntered = current.atomics.firstOrNull()

          edge.getFlatLabels().forEach { label ->
            if (label.references.isNotEmpty()) exit("references")
            when (label) {
              is StmtLabel -> {
                when (val stmt = label.stmt) {
                  is AssignStmt<*> -> {
                    val consts = stmt.expr.toEvents()
                    last = event(stmt.varDecl, EventType.WRITE)
                    last.first().assignment = Eq(last.first().const.ref, stmt.expr.with(consts))
                  }

                  is AssumeStmt -> {
                    val consts =
                      stmt.cond.vars.associateWith { it.threadVar(pid).getNewIndexed(false) } +
                        stmt.cond.dereferences.associateWith { memoryDecl.getNewIndexed(false) }
                    val condWithConsts = stmt.cond.with(consts)
                    val asAssign =
                      consts.size == 1 &&
                        consts.keys.first().let {
                          it is VarDecl<*> && it.threadVar(pid) !in lastWrites
                        }
                    if (edge.source.outgoingEdges.size > 1 || !asAssign) {
                      guard = guard + condWithConsts
                      if (firstLabel) {
                        consts.forEach { (v, c) ->
                          assumeConsts.getOrPut(v) { mutableListOf() }.add(c)
                        }
                      }
                    }
                    stmt.cond.toEvents(consts, false)
                    if (edge.source.outgoingEdges.size == 1 && asAssign) {
                      last.first().assignment = condWithConsts
                    }
                  }

                  is HavocStmt<*> -> {
                    last = event(stmt.varDecl, EventType.WRITE)
                    last.first().assignment = True()
                  }

                  is MemoryAssignStmt<*, *, *> -> {
                    val exprConsts = stmt.expr.toEvents()
                    val arrayConsts = stmt.deref.array.toEvents(exprConsts)
                    val offsetConsts = stmt.deref.offset.toEvents(arrayConsts)
                    last = memoryEvent(stmt.deref, arrayConsts + offsetConsts, EventType.WRITE)
                    last.first().assignment = Eq(last.first().const.ref, stmt.expr.with(exprConsts))
                  }

                  else -> exit("unknown statement type: $stmt")
                }
              }

              is StartLabel -> {
                if (label.name in thread.startHistory) {
                  exit("recursive thread start")
                }
                val procedure =
                  xcfa.procedures.find { it.name == label.name }
                    ?: exit("unknown procedure name: ${label.name}")
                val newPid = Thread.uniqueId()

                // assign parameter
                val consts = label.params[1].toEvents()
                val arg = procedure.params.first { it.second != ParamDirection.OUT }.first
                last = event(arg, EventType.WRITE, newPid)
                last.first().assignment = Eq(last.first().const.ref, label.params[1].with(consts))

                last = event(label.pidVar, EventType.WRITE)
                val pidVar = label.pidVar.threadVar(pid)
                if (threads.any { it.pidVar == pidVar }) {
                  multipleUsePidVars.add(pidVar)
                }
                val newHistory = thread.startHistory + thread.procedure.name
                val newThread =
                  Thread(newPid, procedure, guard, pidVar, last.first(), newHistory, lastWrites)
                last.first().assignment = Eq(last.first().const.ref, Int(newPid))
                threadLookup[pidVar] = setOf(Pair(guard, newThread))
                ThreadProcessor(newThread).process()
              }

              is JoinLabel -> {
                val incomingGuard = guard
                val lastEvents = mutableListOf<E>()
                val joinGuards = mutableListOf<Set<Expr<BoolType>>>()
                val pidVar = label.pidVar.threadVar(pid)
                if (pidVar in multipleUsePidVars) {
                  exit("join on a pthread_t variable used in multiple pthread_create calls")
                }
                threadLookup[pidVar]?.forEach { (g, thread) ->
                  guard = incomingGuard + g + thread.finalEvents.map { it.guard }.toOrInSet()
                  val joinEvent = event(label.pidVar, EventType.READ).first()
                  thread.finalEvents.forEach { final -> po(final, joinEvent) }
                  lastEvents.add(joinEvent)
                  joinGuards.add(guard)
                  thread.joinEvents.add(joinEvent)
                } ?: exit("thread started in a different thread")
                guard = joinGuards.toOrInSet()
                last = lastEvents
              }

              is FenceLabel -> {
                if (
                  label.labels.size > 1 || label.labels.firstOrNull()?.contains("ATOMIC") != true
                ) {
                  if (
                    label.labels.size != 1 ||
                      label.labels.first() != "pthread_exit" ||
                      !edge.target.final
                  ) {
                    exit("untransformed fence label: $label")
                  }
                }
                if (label.isAtomicBegin) atomicEntered = false
                if (label.isAtomicEnd) atomicEntered = null
              }

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
          searchItem.atomics.add(atomicEntered)
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
  }

  private fun addCrossThreadRelations() {
    for ((v, map) in events) {
      if (map.values.all { it.all { e -> e.assignment == null } })
        exit("variable $v is not initialized")
      for ((pid1, list1) in map) for ((pid2, list2) in map) if (pid1 != pid2)
        for (e1 in list1.filter { it.type == EventType.WRITE }) for (e2 in list2) {
          if (e2.type == EventType.READ) rfs.add(RelationType.RF, e1, e2)
          if (e2.type == EventType.WRITE) wss.add(RelationType.WS, e1, e2)
        }
    }
  }

  private fun addToSolver(solver: Solver): Boolean {
    if (violations.isEmpty()) return false

    // Value assignment
    events.values
      .flatMap { it.values.flatten() }
      .filter { it.assignment != null }
      .forEach { event ->
        if (event.guard.isEmpty()) solver.add(event.assignment)
        else solver.add(Imply(event.guardExpr, event.assignment))
      }

    // Branching conditions
    branchingConditions.forEach { solver.add(it) }

    // Property violation
    solver.add(Or(violations.map { it.guard }))

    // RF
    rfs.forEach { (v, list) ->
      list
        .groupBy { it.to }
        .forEach { (event, rels) ->
          rels.forEach { rel ->
            var conseq =
              And(rel.from.guardExpr, rel.to.guardExpr, Eq(rel.from.const.ref, rel.to.const.ref))
            if (v == memoryDecl) {
              conseq =
                And(conseq, Eq(rel.from.array, rel.to.array), Eq(rel.from.offset, rel.to.offset))
            }
            solver.add(Imply(rel.declRef, conseq)) // RF-Val
          }
          solver.add(Imply(event.guardExpr, Or(rels.map { it.declRef }))) // RF-Some
        }
    }

    return true
  }

  // Utility functions

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

  private fun <T : Type> VarDecl<T>.threadVar(pid: Int): VarDecl<T> =
    if (
      this !== memoryDecl && xcfa.globalVars.none { it.wrappedVar == this && !it.threadLocal }
    ) { // if not global var
      cast(
        localVars
          .getOrPut(this) { mutableMapOf() }
          .getOrPut(pid) { Decls.Var("t$pid::$name", type) },
        type,
      )
    } else this

  private fun <T : Type> VarDecl<T>.getNewIndexed(increment: Boolean = true): IndexedConstDecl<T> {
    val constDecl = getConstDecl(indexing.get(this))
    if (increment) indexing = indexing.inc(this)
    return constDecl
  }

  private fun exit(msg: String): Nothing {
    error("Feature not supported by OC checker: $msg.")
  }
}
