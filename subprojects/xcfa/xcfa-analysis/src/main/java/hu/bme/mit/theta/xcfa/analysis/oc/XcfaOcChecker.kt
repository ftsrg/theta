package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.IndexedVarDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.acquiredMutexes
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.releasedMutexes
import java.nio.file.Path
import java.util.*

const val SOLVER_PATH = "/mnt/d/Theta/zord-pldi-version/out/z3"

class XcfaOcChecker(xcfa: XCFA, private val logger: Logger) : SafetyChecker<XcfaState<*>, XcfaAction, UnitPrec> {

    private val xcfa: XCFA = xcfa.toSSA()
    private val ocSolver = OcSolverFactory(Path.of(SOLVER_PATH)).createSolver()
    private val ssaUtils = SSAUtils()

    private val threads = mutableSetOf<Thread>()
    private val events = mutableMapOf<VarDecl<*>, MutableMap<Int, MutableList<Event>>>()
    private val violations = mutableListOf<Violation>() // OR!
    private val branchingConditions = mutableListOf<Expr<BoolType>>()
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

        logger.write(Logger.Level.MAINSTEP, "Adding constraints...\n")
        addConstraints()

        logger.write(Logger.Level.MAINSTEP, "Starting OC checker...\n")
        val status = ocSolver.check()
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
        var inEdge = false

        val newEvent: (VarDecl<*>, EventType) -> List<Event> = { decl, type ->
            val v = (decl as IndexedVarDecl).original
            val e = Event(decl, type, guard, pid)
            last.forEach { po(it, e, mutex, inEdge) }
            inEdge = true
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

        val waitList = mutableSetOf<SearchItem>()
        val toVisit = mutableSetOf(SearchItem(thread.procedure.initLoc).apply {
            guards.add(thread.guard)
            mutexes.add(thread.mutex)
            thread.startEvent?.let { lastEvents.add(it) }
        })
        val threads = mutableListOf<Thread>()

        while (toVisit.isNotEmpty()) {
            val current = toVisit.first()
            toVisit.remove(current)
            check(current.incoming.size == current.loc.incomingEdges.size)
            check(current.incoming.size == current.guards.size || current.loc.initial)
            check(current.incoming.size == current.mutexes.size || current.loc.initial)
            check(current.incoming.size == current.lastWrites.size) // lastEvents intentionally skipped
            check(current.incoming.size == current.pidLookups.size)
            if (current.mutexes.any { it != current.mutexes.first() }) {
                error("Bad pattern: mutex locked only in a subset of branches. Not supported by this checker.")
            }
            val mergeGuards = { // intersection of guard expressions from incoming edges
                current.guards.reduce(listOf()) { g1, g2 -> g1.filter { it in g2 } }
            }
            guard = mergeGuards()

            if (current.loc.error) {
                violations.add(Violation(current.loc, And(guard), current.lastEvents))
                continue
            }

            if (current.loc.final) {
                current.lastEvents.forEach { final ->
                    thread.joinEvents.forEach { join -> po(final, join, current.mutexes.first()) }
                }
            }

            if (current.loc.outgoingEdges.size > 1) {
                val branchingConditionVars = mutableMapOf<VarDecl<*>, MutableSet<VarDecl<*>>>()
                for (edge in current.loc.outgoingEdges) {
                    val first = edge.getFlatLabels().first()
                    if (first !is StmtLabel || first.stmt !is AssumeStmt) {
                        error("Branching with non-assume labels not supported by this checker.")
                    }
                    first.collectVars().forEach { v ->
                        branchingConditionVars.getOrPut((v as IndexedVarDecl).original) { mutableSetOf() }.add(v)
                    }
                }
                branchingConditionVars.forEach { (_, set) ->
                    for ((i1, v1) in set.withIndex())
                        for ((i2, v2) in set.withIndex()) {
                            if (i1 == i2) break
                            branchingConditions.add(Eq(v1.constRef, v2.constRef))
                        }
                }
            }

            for (edge in current.loc.outgoingEdges) {
                inEdge = false
                last = current.lastEvents
                guard = mergeGuards()
                mutex = current.mutexes.first()
                lastWrites = current.lastWrites.merge().toMutableMap()
                val pidLookup = current.pidLookups.merge { s1, s2 ->
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
                                    last.first().assignment = Eq(stmt.varDecl.constRef, stmt.expr.withConsts())
                                }

                                is AssumeStmt -> {
                                    if (edge.source.outgoingEdges.size > 1) // TODO remove this condition
                                        guard = guard + stmt.cond.withConsts()
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
                            last.first().assignment = Eq(label.pidVar.constRef, Int(newThread.pid))
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

                val searchItem = waitList.find { it.loc == edge.target }
                    ?: SearchItem(edge.target).apply { waitList.add(this) }
                searchItem.guards.add(guard)
                searchItem.mutexes.add(mutex)
                searchItem.lastEvents.addAll(last)
                searchItem.lastWrites.add(lastWrites)
                searchItem.pidLookups.add(pidLookup)
                searchItem.incoming.add(edge)
                if (searchItem.incoming.size == searchItem.loc.incomingEdges.size) {
                    waitList.remove(searchItem)
                    toVisit.add(searchItem)
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

        // Branching conditions
        branchingConditions.forEach { ocSolver.add(it) }

        // Property violation
        ocSolver.add(Or(violations.map { it.guard }))

        // Program order
        ocSolver.add(pos)

        // RF
        rfs.forEach { (_, list) ->
            list.groupBy { it.to }.forEach { (event, rels) ->
                rels.forEach { rel ->
                    ocSolver.add(Imply(rel.declRef,
                        And(And(rel.from.guard), And(rel.to.guard), Eq(rel.from.decl.constRef, rel.to.decl.constRef))
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
        val eventTrace = getEventTrace(model)
        val valuation = model.toMap()
        val edges = xcfa.procedures.flatMap { it.edges }

        val processes = events.values.fold(mapOf<Int, Event>()) { acc, map ->
            (acc.keys + map.keys).associateWith { k -> acc[k] ?: map[k]!!.first() }
        }.map { (pid, event) ->
            pid to XcfaProcessState(
                locs = LinkedList(listOf(
                    xcfa.procedures.find { p -> p.edges.any { event.decl in it.label.collectVars() } }!!.initLoc
                )),
                varLookup = LinkedList(emptyList())
            )
        }.toMap()
        var explState = ExplState.of(ImmutableValuation.from(mapOf()))
        var state = XcfaState<ExplState>(xcfa, processes, explState)
        stateList.add(state)
        var lastEdge: XcfaEdge? = edges.find { eventTrace[0].decl in it.label.collectVars() }

        for ((index, event) in eventTrace.withIndex()) {
            valuation[event.decl.const]?.let {
                val newVal = explState.`val`.toMap().toMutableMap().apply { put(event.decl.original, it) }
                explState = ExplState.of(ImmutableValuation.from(newVal))
            }

            val nextEdge = eventTrace.getOrNull(index + 1)?.let { e -> edges.find { e.decl in it.label.collectVars() } }
            if (nextEdge != lastEdge) {
                actionList.add(XcfaAction(event.pid, ssaUtils.removeSSA(lastEdge!!)))
                state = state.copy(
                    processes = state.processes.toMutableMap().apply {
                        put(event.pid, XcfaProcessState(
                            locs = LinkedList(listOf(lastEdge!!.target)),
                            varLookup = LinkedList(emptyList())
                        ))
                    },
                    sGlobal = explState
                )
                stateList.add(state)
                lastEdge = nextEdge
            }
        }
        return Trace.of(stateList, actionList)
    }

    private fun getEventTrace(model: Valuation): List<Event> {
        val valuation = model.toMap()
        val previousEvents: Collection<Relation>.(Event) -> Collection<Event> = { event ->
            filter { it.to == event && it.enabled(valuation) && it.from.enabled(model) }.map { it.from }
        }
        val violation = violations.first { (it.guard.eval(model) as BoolLitExpr).value }

        val startEvents = violation.lastEvents.toMutableList()
        val finished = mutableListOf<Event>() // topological order
        while (startEvents.isNotEmpty()) { // DFS from startEvents as root nodes
            val stack = Stack<StackItem>()
            stack.push(StackItem(startEvents.removeFirst()))
            while (stack.isNotEmpty()) {
                val top = stack.peek()
                if (top.eventsToVisit == null) {
                    val previous = mutableSetOf<Event>()
                    previous.addAll(pos.previousEvents(top.event))
                    when (top.event.type) {
                        EventType.WRITE -> cos[top.event.decl.original]?.previousEvents(top.event)
                        EventType.READ -> rfs[top.event.decl.original]?.previousEvents(top.event)
                    }?.let { previous.addAll(it) }
                    top.eventsToVisit = previous.toMutableList()
                }

                if (top.eventsToVisit!!.isEmpty()) {
                    stack.pop()
                    finished.add(top.event)
                    continue
                }

                val visiting = top.eventsToVisit!!.removeFirst()
                if (visiting !in finished) {
                    stack.push(StackItem(visiting))
                }
            }
        }
        return finished
    }

    // Utility functions

    private fun po(from: Event?, to: Event, mutex: Mutex? = null, inEdge: Boolean = false) {
        if (from == null) return
        val relation = if (!inEdge && (mutex == null || !mutex.entered)) {
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

    private val VarDecl<*>.constRef get() = (this as IndexedVarDecl).constRef

    private fun <T : Type> Expr<T>.withConsts(): Expr<T> {
        if (this is RefExpr<T>) {
            return (decl as? IndexedVarDecl<T>)?.constRef ?: this
        }
        return map { it.withConsts() }
    }
}
