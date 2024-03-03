package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.core.decl.IndexedVarDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.acquiredMutexes
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.releasedMutexes
import java.nio.file.Path

const val SOLVER_PATH = "/mnt/d/Theta/zord-pldi-version/out/z3"

class XcfaOcChecker(private val xcfa: XCFA) : SafetyChecker<XcfaState<*>, XcfaAction, UnitPrec> {

    private val ocSolver = OcSolverFactory(Path.of(SOLVER_PATH)).createSolver()

    private val threads = mutableSetOf<Thread>()
    private val events = mutableMapOf<VarDecl<*>, MutableMap<Int, MutableList<Event>>>()
    private val violations = mutableListOf<Expr<BoolType>>() // OR!
    private val pos = mutableListOf<Relation>()
    private val rfs = mutableMapOf<VarDecl<*>, MutableList<Relation>>()
    private val cos = mutableMapOf<VarDecl<*>, MutableList<Relation>>()

    override fun check(prec: UnitPrec?): SafetyResult<XcfaState<*>, XcfaAction> {
        if (xcfa.initProcedures.size > 1) error("Multiple entry points are not supported by this checker.")
        val usedMutexes = mutableSetOf<String>()
        xcfa.procedures.forEach { p ->
            p.edges.forEach { edge ->
                edge.label.getFlatLabels().filterIsInstance<FenceLabel>()
                    .forEach { usedMutexes.addAll(it.acquiredMutexes) }
            }
        }
        if (usedMutexes.size > 1) error("Multiple mutexes are not supported by this checker.")

        addConstraints()
//        System.err.println(xcfa.toDot())

        val status = ocSolver.check()
        System.err.println(status)
        return when {
            status.isUnsat -> SafetyResult.safe()
            status.isSat -> SafetyResult.unsafe(getTrace(ocSolver.model))
            else -> SafetyResult.unknown()
        }
    }

    private fun addConstraints() {
        val threads = xcfa.initProcedures.map { Thread(it.first) }.toMutableSet()
        this.threads.addAll(threads)
        while (threads.isNotEmpty()) {
            val thread = threads.first()
            threads.remove(thread)
            val newThreads = processThread(thread)
            threads.addAll(newThreads)
            this.threads.addAll(newThreads)
        }

        addCrossThreadRelations()
        addToSolver()
    }

    private fun processThread(thread: Thread): List<Thread> {
        val pid = thread.pid
        var last = listOf<Event>()
        var guard = listOf<Expr<BoolType>>()
        var mutex: Mutex? = null
        var lastWrites: MutableMap<VarDecl<*>, Set<Event>> = mutableMapOf()

        val newEvent: (VarDecl<*>, EventType) -> List<Event> = { decl, type ->
            val v = (decl as IndexedVarDecl).original
            val e = Event(decl, type, guard, pid)
            last.forEach { po(it, e, mutex) }
            when (type) {
                EventType.READ -> lastWrites[v]?.forEach { rfs.add(RelationType.RFI, it, e) }
                EventType.WRITE -> {
                    lastWrites[v]?.forEach { cos.add(RelationType.COI, it, e) }
                    lastWrites[v] = setOf(e)
                }
            }
            events[v] = (events[v] ?: mutableMapOf()).apply {
                this[pid] = (this[pid] ?: mutableListOf()).apply { add(e) }
            }
            listOf(e)
        }

        val waitList = mutableSetOf<StackItem>()
        val toVisit = mutableSetOf(StackItem(thread.procedure.initLoc).apply {
            guards.add(thread.guard)
            mutexes.add(thread.mutex)
            thread.startEvent?.let { lastEvents.add(it) }
        })
        val threads = mutableListOf<Thread>()

        while (toVisit.isNotEmpty()) {
            val top = toVisit.first()
            toVisit.remove(top)
            check(top.incoming.size == top.loc.incomingEdges.size)
            check(top.incoming.size == top.guards.size || top.loc.initial)
            check(top.incoming.size == top.mutexes.size || top.loc.initial)
            check(top.incoming.size == top.lastWrites.size) // lastEvents intentionally skipped
            check(top.incoming.size == top.pidLookups.size)
            if (top.mutexes.any { it != top.mutexes.first() }) {
                error("Bad pattern: mutex locked only in a subset of branches. Not supported by this checker.")
            }
            val mergeGuards = { // intersection of guard expressions from incoming edges
                top.guards.reduce(listOf()) { g1, g2 -> g1.filter { it in g2 } }
            }
            guard = mergeGuards()

            if (top.loc.error) {
                violations.add(And(guard))
                continue
            }

            if (top.loc.final) {
                top.lastEvents.forEach { final ->
                    thread.joinEvents.forEach { join -> po(final, join, top.mutexes.first()) }
                }
            }

            for (edge in top.loc.outgoingEdges) {
                last = top.lastEvents
                guard = mergeGuards()
                mutex = top.mutexes.first()
                lastWrites = top.lastWrites.merge().toMutableMap()
                val pidLookup = top.pidLookups.merge { s1, s2 ->
                    s1 + s2.filter { (guard2, _) -> s1.none { (guard1, _) -> guard1 == guard2 } }
                }.toMutableMap()

                edge.getFlatLabels().forEach { label ->
                    when (label) {
                        is StmtLabel -> {
                            when (val stmt = label.stmt) {
                                is AssignStmt<*> -> {
                                    stmt.expr.vars.forEach {
                                        last = newEvent(it, EventType.READ)
                                    }
                                    last = newEvent(stmt.varDecl, EventType.WRITE)
                                    last.first().assignment = Eq(stmt.varDecl.ref, stmt.expr)
                                }

                                is AssumeStmt -> {
                                    if (edge.source.outgoingEdges.size > 1) // TODO remove this condition
                                        guard = guard + stmt.cond
                                    stmt.cond.vars.forEach {
                                        last = newEvent(it, EventType.READ)
                                    }
                                }

                                is HavocStmt<*> -> {
                                    last = newEvent(stmt.varDecl, EventType.WRITE)
                                }

                                else -> error("Unsupported statement type: $stmt")
                            }
                        }

                        is StartLabel -> {
                            val procedure = xcfa.procedures.find { it.name == label.name }
                                ?: error("Procedure not found: ${label.name}")
                            last = newEvent(label.pidVar, EventType.WRITE)
                            val pidVar = (label.pidVar as IndexedVarDecl).original
                            if (this.threads.any { it.pidVar == pidVar }) {
                                error("Multi-thread use of pthread_t variables are not supported by this checker.")
                            }
                            val newThread = Thread(procedure, guard, mutex, pidVar, last.first())
                            last.first().assignment = Eq(label.pidVar.ref, Int(newThread.pid))
                            pidLookup[pidVar] = setOf(Pair(guard, newThread.pid))
                            threads.add(newThread)
                        }

                        is JoinLabel -> {
                            val pidVar = (label.pidVar as IndexedVarDecl).original
                            val guardTemp = guard
                            val lastEvents = mutableListOf<Event>()
                            pidLookup[pidVar]?.forEach { (g, pid) ->
                                guard = g
                                lastEvents.addAll(newEvent(label.pidVar, EventType.READ))
                                threads.find { it.pid == pid }?.joinEvents?.add(lastEvents.last())
                            } ?: error("Thread started in a different thread: not supported by this checker.")
                            guard = guardTemp
                            last = lastEvents
                        }

                        is FenceLabel -> {
                            label.acquiredMutexes.firstOrNull()?.let { mutex = Mutex(it) }
                            label.releasedMutexes.firstOrNull()?.let { mutex = null }
                        }

                        is NopLabel -> {}
                        else -> error("Unsupported label type: $label")
                    }
                }

                val stackItem = waitList.find { it.loc == edge.target }
                    ?: StackItem(edge.target).apply { waitList.add(this) }
                stackItem.guards.add(guard)
                stackItem.mutexes.add(mutex)
                stackItem.lastEvents.addAll(last)
                stackItem.lastWrites.add(lastWrites)
                stackItem.pidLookups.add(pidLookup)
                stackItem.incoming.add(edge)
                if (stackItem.incoming.size == stackItem.loc.incomingEdges.size) {
                    waitList.remove(stackItem)
                    toVisit.add(stackItem)
                }
            }
        }

        if (waitList.isNotEmpty()) error("Loops and dangling edges not supported by this checker.")
        return threads
    }

    private fun addCrossThreadRelations() {
        for ((_, map) in events)
            for ((pid1, list1) in map)
                for ((pid2, list2) in map)
                    if (pid1 != pid2)
                        for (e1 in list1.filter { it.type == EventType.WRITE })
                            for (e2 in list2)
                                when (e2.type) {
                                    EventType.WRITE -> cos.add(RelationType.COE, e1, e2)
                                    EventType.READ -> rfs.add(RelationType.RFE, e1, e2)
                                }
    }

    private fun addToSolver() {
        // Value assignment
        events.values.flatMap { it.values.flatten() }.filter { it.assignment != null }.forEach { event ->
            when (event.guard.size) {
                0 -> ocSolver.add(event.assignment)
                1 -> ocSolver.add(Imply(event.guard.first(), event.assignment))
                else -> ocSolver.add(Imply(And(event.guard), event.assignment))
            }
        }

        // Property violation
        ocSolver.add(Or(violations))

        // Program order
        ocSolver.add(pos)

        // RF
        rfs.forEach { (_, list) ->
            list.groupBy { it.to }.forEach { (event, rels) ->
                rels.forEach { rel ->
                    ocSolver.add(Imply(rel.declRef,
                        And(And(rel.from.guard), And(rel.to.guard), Eq(rel.from.decl.ref, rel.to.decl.ref))
                    )) // RF-Val
                    ocSolver.add(Imply(rel.declRef, rel)) // RF-Ord
                }
                ocSolver.add(Imply(And(event.guard), Or(rels.map { it.declRef }))) // RF-Some
            }
        }

        // CO
        cos.forEach { (_, list) ->
            val paired = mutableListOf<Relation>()
            for ((i1, rel1) in list.withIndex()) {
                ocSolver.add(Imply(rel1.declRef, And(And(rel1.from.guard), And(rel1.to.guard)))) // WS-Cond
                ocSolver.add(Imply(rel1.declRef, rel1)) // WS-Ord

                for ((i2, rel2) in list.withIndex()) {
                    if (i1 == i2) break
                    if (rel1.from == rel2.to && rel1.to == rel2.from) {
                        ocSolver.add(Imply(And(And(rel1.from.guard), And(rel1.to.guard)),
                            Or(rel1.declRef, rel2.declRef))) // WS-Some
                        paired.add(rel1)
                        paired.add(rel2)
                        break
                    }
                }
            }
            (list - paired.toSet()).forEach { rel ->
                ocSolver.add(Imply(And(And(rel.from.guard), And(rel.to.guard)), rel.declRef)) // WS-Some
            }
        }
    }

    private fun getTrace(model: Valuation): Trace<XcfaState<*>, XcfaAction> {
        val stateList = mutableListOf<XcfaState<*>>()
        val actionList = mutableListOf<XcfaAction>()
        
        return Trace.of(stateList, actionList)
    }

    private val Expr<*>.vars get() = ExprUtils.getVars(this)

    private fun po(from: Event?, to: Event, mutex: Mutex? = null) {
        if (from == null) return
        val relation = if (mutex == null || !mutex.entered) {
            mutex?.let { it.entered = true }
            Relation(RelationType.PO, from, to)
        } else {
            Relation(RelationType.EPO, from, to)
        }
        pos.add(relation)
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

    private fun MutableMap<VarDecl<*>, MutableList<Relation>>.add(type: RelationType, from: Event, to: Event) =
        getOrPut(from.decl.original) { mutableListOf() }.add(Relation(type, from, to))

}
