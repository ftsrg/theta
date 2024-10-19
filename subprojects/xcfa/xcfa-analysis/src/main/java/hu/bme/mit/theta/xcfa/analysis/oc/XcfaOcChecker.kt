/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyWitness
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.analysis.algorithm.oc.OcChecker
import hu.bme.mit.theta.analysis.algorithm.oc.Relation
import hu.bme.mit.theta.analysis.algorithm.oc.RelationType
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.*
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.AssumeFalseRemovalPass
import hu.bme.mit.theta.xcfa.passes.AtomicReadsOneWritePass
import hu.bme.mit.theta.xcfa.passes.MutexToVarPass

private val Expr<*>.vars get() = ExprUtils.getVars(this)

class XcfaOcChecker(xcfa: XCFA, decisionProcedure: OcDecisionProcedureType, private val logger: Logger) :
    SafetyChecker<EmptyWitness, Trace<XcfaState<out PtrState<*>>, XcfaAction>, XcfaPrec<UnitPrec>> {

    private val ocChecker: OcChecker<E> = decisionProcedure.checker()
    private val solver = ocChecker.solver

    private val xcfa: XCFA = xcfa.optimizeFurther(
        listOf(AssumeFalseRemovalPass(), MutexToVarPass(), AtomicReadsOneWritePass())
    )
    private var indexing = VarIndexingFactory.indexing(0)
    private val localVars = mutableMapOf<VarDecl<*>, MutableMap<Int, VarDecl<*>>>()

    private val threads = mutableSetOf<Thread>()
    private val events = mutableMapOf<VarDecl<*>, MutableMap<Int, MutableList<E>>>()
    private val violations = mutableListOf<Violation>() // OR!
    private val branchingConditions = mutableListOf<Expr<BoolType>>()
    private val pos = mutableListOf<R>()
    private val rfs = mutableMapOf<VarDecl<*>, MutableSet<R>>()

    override fun check(
        prec: XcfaPrec<UnitPrec>?): SafetyResult<EmptyWitness, Trace<XcfaState<out PtrState<*>>, XcfaAction>> = let {
        if (xcfa.initProcedures.size > 1) error("Multiple entry points are not supported by OC checker.")

        logger.write(Logger.Level.MAINSTEP, "Adding constraints...\n")
        xcfa.initProcedures.forEach { processThread(Thread(it.first)) }
        addCrossThreadRelations()
        if (!addToSolver()) return@let SafetyResult.safe<EmptyWitness, Trace<XcfaState<out PtrState<*>>, XcfaAction>>(
            EmptyWitness.getInstance()) // no violations in the model

        logger.write(Logger.Level.MAINSTEP, "Start checking...\n")
        val status = ocChecker.check(events, pos, rfs)
        when {
            status?.isUnsat == true -> SafetyResult.safe(EmptyWitness.getInstance())
            status?.isSat == true -> SafetyResult.unsafe(
                XcfaOcTraceExtractor(xcfa, ocChecker, threads, events, violations, pos).trace,
                EmptyWitness.getInstance()
            )

            else -> SafetyResult.unknown()
        }
    }.also { logger.write(Logger.Level.MAINSTEP, "OC checker result: $it\n") }

    private fun processThread(thread: Thread): List<Thread> {
        threads.add(thread)
        val pid = thread.pid
        var last = listOf<E>()
        var guard = setOf<Expr<BoolType>>()
        lateinit var lastWrites: MutableMap<VarDecl<*>, Set<E>>
        lateinit var edge: XcfaEdge
        var inEdge = false
        var atomicEntered: Boolean? = null

        val newEvent: (VarDecl<*>, EventType) -> List<E> = { d, type ->
            check(!inEdge || last.size == 1)
            val decl = d.threadVar(pid)
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
            events[decl] = (events[decl] ?: mutableMapOf()).apply {
                this[pid] = (this[pid] ?: mutableListOf()).apply { add(e) }
            }
            listOf(e)
        }

        val waitList = mutableSetOf<SearchItem>()
        val toVisit = mutableSetOf(SearchItem(thread.procedure.initLoc).apply {
            guards.add(thread.guard)
            thread.startEvent?.let { lastEvents.add(it) }
            this.lastWrites.add(thread.lastWrites)
        })
        val threads = mutableListOf<Thread>()

        while (toVisit.isNotEmpty()) {
            val current = toVisit.first()
            toVisit.remove(current)
            check(current.incoming == current.loc.incomingEdges.size)
            check(current.incoming == current.guards.size || current.loc.initial)
            // lastEvents intentionally skipped
            check(current.incoming == current.lastWrites.size || current.loc.initial)
            check(current.incoming == current.threadLookups.size)
            check(current.incoming == current.atomics.size)
            check(current.atomics.all { it == current.atomics.first() }) // bad pattern otherwise

            if (current.loc.error) {
                val errorGuard = Or(current.lastEvents.map { it.guard.toAnd() })
                violations.add(Violation(current.loc, pid, errorGuard, current.lastEvents))
                continue
            }

            if (current.loc.final) {
                thread.finalEvents.addAll(current.lastEvents)
            }

            val mergedGuard = current.guards.toOrInSet()
            val assumeConsts = mutableMapOf<VarDecl<*>, MutableList<ConstDecl<*>>>()

            for (e in current.loc.outgoingEdges) {
                edge = e
                inEdge = false
                last = current.lastEvents
                // intersection of guards of incoming edges:
                guard = mergedGuard
                lastWrites = current.lastWrites.merge().toMutableMap()
                val threadLookup = current.threadLookups.merge { s1, s2 ->
                    s1 + s2.filter { (guard2, _) -> s1.none { (guard1, _) -> guard1 == guard2 } }
                }.toMutableMap()
                var firstLabel = true
                atomicEntered = current.atomics.firstOrNull()

                edge.getFlatLabels().forEach { label ->
                    if (label.references.isNotEmpty() || label.dereferences.isNotEmpty()) {
                        error("References not supported by OC checker.")
                    }
                    when (label) {
                        is StmtLabel -> {
                            when (val stmt = label.stmt) {
                                is AssignStmt<*> -> {
                                    val consts = mutableMapOf<VarDecl<*>, ConstDecl<*>>()
                                    stmt.expr.vars.forEach {
                                        last = newEvent(it, EventType.READ)
                                        consts[it] = last.first().const
                                    }
                                    last = newEvent(stmt.varDecl, EventType.WRITE)
                                    last.first().assignment = Eq(last.first().const.ref, stmt.expr.withConsts(consts))
                                }

                                is AssumeStmt -> {
                                    val consts = stmt.cond.vars.associateWith { it.threadVar(pid).getNewIndexed(false) }
                                    val condWithConsts = stmt.cond.withConsts(consts)
                                    val asAssign = consts.size == 1 && consts.keys.first().threadVar(pid) !in lastWrites
                                    if (edge.source.outgoingEdges.size > 1 || !asAssign) {
                                        guard = guard + condWithConsts
                                        if (firstLabel) {
                                            consts.forEach { (v, c) ->
                                                assumeConsts.getOrPut(v) { mutableListOf() }.add(c)
                                            }
                                        }
                                    }
                                    stmt.cond.vars.forEach {
                                        last = newEvent(it, EventType.READ)
                                    }
                                    if (edge.source.outgoingEdges.size == 1 && asAssign) {
                                        last.first().assignment = condWithConsts
                                    }
                                }

                                is HavocStmt<*> -> {
                                    last = newEvent(stmt.varDecl, EventType.WRITE)
                                }

                                else -> error("Unsupported statement type: $stmt")
                            }
                        }

                        is StartLabel -> {
                            // TODO StartLabel params
                            if (label.name in thread.startHistory) {
                                error("Recursive thread start not supported by OC checker.")
                            }
                            val procedure = xcfa.procedures.find { it.name == label.name }
                                ?: error("Procedure not found: ${label.name}")
                            last = newEvent(label.pidVar, EventType.WRITE)
                            val pidVar = label.pidVar.threadVar(pid)
                            if (this.threads.any { it.pidVar == pidVar }) {
                                error("Using a pthread_t variable in multiple threads is not supported by OC checker.")
                            }
                            val newHistory = thread.startHistory + thread.procedure.name
                            val newThread = Thread(procedure, guard, pidVar, last.first(), newHistory, lastWrites)
                            last.first().assignment = Eq(last.first().const.ref, Int(newThread.pid))
                            threadLookup[pidVar] = setOf(Pair(guard, newThread))
                            processThread(newThread)
                        }

                        is JoinLabel -> {
                            val incomingGuard = guard
                            val lastEvents = mutableListOf<E>()
                            val joinGuards = mutableListOf<Set<Expr<BoolType>>>()
                            threadLookup[label.pidVar.threadVar(pid)]?.forEach { (g, thread) ->
                                guard = incomingGuard + g + thread.finalEvents.map { it.guard }.toOrInSet()
                                val joinEvent = newEvent(label.pidVar, EventType.READ).first()
                                thread.finalEvents.forEach { final -> po(final, joinEvent) }
                                lastEvents.add(joinEvent)
                                joinGuards.add(guard)
                            } ?: error("Thread started in a different thread: not supported by OC checker.")
                            guard = joinGuards.toOrInSet()
                            last = lastEvents
                        }

                        is FenceLabel -> {
                            if (label.labels.size > 1 || label.labels.firstOrNull()?.contains("ATOMIC") != true) {
                                error("Untransformed fence label: $label")
                            }
                            if (label.isAtomicBegin) atomicEntered = false
                            if (label.isAtomicEnd) atomicEntered = null
                        }

                        is NopLabel -> {}
                        else -> error("Unsupported label type by OC checker: $label")
                    }
                    firstLabel = false
                }

                val searchItem = waitList.find { it.loc == edge.target }
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
                        error("Branching with non-assume labels not supported by OC checker.")
                    }
                }
                assumeConsts.forEach { (_, set) ->
                    for ((i1, v1) in set.withIndex())
                        for ((i2, v2) in set.withIndex()) {
                            if (i1 == i2) break
                            branchingConditions.add(Eq(v1.ref, v2.ref))
                        }
                }
            }
        }

        if (waitList.isNotEmpty()) error("Loops and dangling edges not supported by OC checker.")
        return threads
    }

    private fun addCrossThreadRelations() {
        for ((_, map) in events)
            for ((pid1, list1) in map)
                for ((pid2, list2) in map)
                    if (pid1 != pid2)
                        for (e1 in list1.filter { it.type == EventType.WRITE })
                            for (e2 in list2.filter { it.type == EventType.READ })
                                rfs.add(RelationType.RF, e1, e2)
    }

    private fun addToSolver(): Boolean {
        if (violations.isEmpty()) return false

        // Value assignment
        events.values.flatMap { it.values.flatten() }.filter { it.assignment != null }.forEach { event ->
            if (event.guard.isEmpty()) solver.add(event.assignment)
            else solver.add(Imply(event.guardExpr, event.assignment))
        }

        // Branching conditions
        branchingConditions.forEach { solver.add(it) }

        // Property violation
        solver.add(Or(violations.map { it.guard }))

        // RF
        rfs.forEach { (_, list) ->
            list.groupBy { it.to }.forEach { (event, rels) ->
                rels.forEach { rel ->
                    solver.add(
                        Imply(
                            rel.declRef,
                            And(rel.from.guardExpr, rel.to.guardExpr, Eq(rel.from.const.ref, rel.to.const.ref))
                        )
                    ) // RF-Val
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

    private fun <K, V> List<Map<K, Set<V>>>.merge(merge: (Set<V>, Set<V>) -> Set<V> = { a, b -> a + b }) =
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

    private fun <T : Type> Expr<T>.withConsts(varToConst: Map<out Decl<*>, ConstDecl<*>>): Expr<T> {
        if (this is RefExpr<T>) {
            return varToConst[decl]?.ref?.let { cast(it, type) } ?: this
        }
        return map { it.withConsts(varToConst) }
    }

    private fun <T : Type> VarDecl<T>.threadVar(pid: Int): VarDecl<T> =
        if (xcfa.vars.none { it.wrappedVar == this && !it.threadLocal }) { // if not global var
            cast(localVars.getOrPut(this) { mutableMapOf() }.getOrPut(pid) {
                Decls.Var("t$pid::$name", type)
            }, type)
        } else this

    private fun <T : Type> VarDecl<T>.getNewIndexed(increment: Boolean = true): IndexedConstDecl<T> {
        val constDecl = getConstDecl(indexing.get(this))
        if (increment) indexing = indexing.inc(this)
        return constDecl
    }
}
