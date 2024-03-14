package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.IndexedConstDecl
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
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.AssumeFalseRemovalPass
import hu.bme.mit.theta.xcfa.passes.MutexToVarPass
import java.nio.file.Path
import java.util.*

private val Expr<*>.vars get() = ExprUtils.getVars(this)

class XcfaOcChecker(xcfa: XCFA, private val logger: Logger, solverHome: String) :
    SafetyChecker<XcfaState<*>, XcfaAction, UnitPrec> {

    private val xcfa: XCFA = xcfa.optimizeFurther(listOf(AssumeFalseRemovalPass(), MutexToVarPass()))
    private val ocSolver = OcSolverFactory(Path.of("$solverHome/z3")).createSolver()
    private val solver = Z3SolverFactory.getInstance().createSolver();
    private var indexing = VarIndexingFactory.indexing(0)

    private val threads = mutableSetOf<Thread>()
    private val events = mutableMapOf<VarDecl<*>, MutableMap<Int, MutableList<Event>>>()
    private val violations = mutableListOf<Violation>() // OR!
    private val branchingConditions = mutableListOf<Expr<BoolType>>()
    private val pos = mutableListOf<Relation>()
    private val rfs = mutableMapOf<VarDecl<*>, MutableList<Relation>>()

    override fun check(prec: UnitPrec?): SafetyResult<XcfaState<*>, XcfaAction> {
        if (xcfa.initProcedures.size > 1) error("Multiple entry points are not supported by this checker.")

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
        lateinit var lastWrites: MutableMap<VarDecl<*>, Set<Event>>
        lateinit var edge: XcfaEdge
        var inEdge = false

        val newEvent: (VarDecl<*>, EventType) -> List<Event> = { decl, type ->
            val e = Event(decl.getNewIndexed(), type, guard, pid, edge)
            last.forEach { po(it, e, inEdge) }
            inEdge = true
            when (type) {
                EventType.READ -> lastWrites[decl]?.forEach { rfs.add(RelationType.RFI, it, e) }
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
        })
        val threads = mutableListOf<Thread>()

        while (toVisit.isNotEmpty()) {
            val current = toVisit.first()
            toVisit.remove(current)
            check(current.incoming.size == current.loc.incomingEdges.size)
            check(current.incoming.size == current.guards.size || current.loc.initial)
            check(current.incoming.size == current.lastWrites.size) // lastEvents intentionally skipped
            check(current.incoming.size == current.pidLookups.size)
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
                    thread.joinEvents.forEach { join -> po(final, join) }
                }
            }

            val assumeConsts = mutableMapOf<VarDecl<*>, MutableList<ConstDecl<*>>>()
            for (e in current.loc.outgoingEdges) {
                edge = e
                inEdge = false
                last = current.lastEvents
                guard = mergeGuards()
                lastWrites = current.lastWrites.merge().toMutableMap()
                val pidLookup = current.pidLookups.merge { s1, s2 ->
                    s1 + s2.filter { (guard2, _) -> s1.none { (guard1, _) -> guard1 == guard2 } }
                }.toMutableMap()
                var firstLabel = true

                edge.getFlatLabels().forEach { label ->
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
//                                    if (edge.source.outgoingEdges.size > 1) { // TODO remove this condition
                                    val consts = stmt.cond.vars.associateWith { it.getNewIndexed(false) }
                                    guard = guard + stmt.cond.withConsts(consts)
                                    if (firstLabel) {
                                        consts.forEach { (v, c) ->
                                            assumeConsts.getOrPut(v) { mutableListOf() }.add(c)
                                        }
                                    }
//                                    }
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
                            if (this.threads.any { it.pidVar == label.pidVar }) {
                                error("Multi-thread use of pthread_t variables are not supported by this checker.")
                            }
                            val newThread = Thread(procedure, guard, label.pidVar, last.first())
                            last.first().assignment = Eq(last.first().const.ref, Int(newThread.pid))
                            pidLookup[label.pidVar] = setOf(Pair(guard, newThread.pid))
                            threads.add(newThread)
                        }

                        is JoinLabel -> {
                            val pidVar = label.pidVar
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

                        is NopLabel -> {}
                        is FenceLabel -> error("Untransformed fence label: $label")
                        else -> error("Unsupported label type by this checker: $label")
                    }
                    firstLabel = false
                }

                val searchItem = waitList.find { it.loc == edge.target }
                    ?: SearchItem(edge.target).apply { waitList.add(this) }
                searchItem.guards.add(guard)
                searchItem.lastEvents.addAll(last)
                searchItem.lastWrites.add(lastWrites)
                searchItem.pidLookups.add(pidLookup)
                searchItem.incoming.add(edge)
                if (searchItem.incoming.size == searchItem.loc.incomingEdges.size) {
                    waitList.remove(searchItem)
                    toVisit.add(searchItem)
                }
            }

            if (current.loc.outgoingEdges.size > 1) {
                for (e in current.loc.outgoingEdges) {
                    val first = e.getFlatLabels().first()
                    if (first !is StmtLabel || first.stmt !is AssumeStmt) {
                        error("Branching with non-assume labels not supported by this checker.")
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

        if (waitList.isNotEmpty()) error("Loops and dangling edges not supported by this checker.")
        return threads
    }

    private fun addCrossThreadRelations() {
        for ((_, map) in events)
            for ((pid1, list1) in map)
                for ((pid2, list2) in map)
                    if (pid1 != pid2)
                        for (e1 in list1.filter { it.type == EventType.WRITE })
                            for (e2 in list2.filter { it.type == EventType.READ })
                                rfs.add(RelationType.RFE, e1, e2)
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
                        And(And(rel.from.guard), And(rel.to.guard), Eq(rel.from.const.ref, rel.to.const.ref))
                    )) // RF-Val
                    ocSolver.add(Imply(rel.declRef, rel)) // RF-Ord
                }
                ocSolver.add(Imply(And(event.guard), Or(rels.map { it.declRef }))) // RF-Some
            }
        }
    }

    private fun getTrace(model: Valuation): Trace<XcfaState<*>, XcfaAction> {
        val stateList = mutableListOf<XcfaState<*>>()
        val actionList = mutableListOf<XcfaAction>()
        val eventTrace = getEventTrace(model)
        val valuation = model.toMap()

        val processes = events.values.fold(mapOf<Int, Event>()) { acc, map ->
            (acc.keys + map.keys).associateWith { k -> acc[k] ?: map[k]!!.first() }
        }.map { (pid, event) ->
            pid to XcfaProcessState(
                locs = LinkedList(listOf(
                    xcfa.procedures.find { p -> p.edges.any { event.const.varDecl in it.label.collectVars() } }!!.initLoc
                )),
                varLookup = LinkedList(emptyList())
            )
        }.toMap()
        var explState = ExplState.of(ImmutableValuation.from(mapOf()))
        var state = XcfaState<ExplState>(xcfa, processes, explState)
        stateList.add(state)
        var lastEdge: XcfaEdge? = eventTrace[0].edge

        for ((index, event) in eventTrace.withIndex()) {
            valuation[event.const]?.let {
                val newVal = explState.`val`.toMap().toMutableMap().apply { put(event.const.varDecl, it) }
                explState = ExplState.of(ImmutableValuation.from(newVal))
            }

            val nextEdge = eventTrace.getOrNull(index + 1)?.edge
            if (nextEdge != lastEdge) {
                actionList.add(XcfaAction(event.pid, lastEdge!!))
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
            filter { it.to == event && it.enabled(valuation) && it.from.enabled(model) == true }.map { it.from }
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
                    if (top.event.type == EventType.READ) {
                        rfs[top.event.const.varDecl]?.previousEvents(top.event)?.let { previous.addAll(it) }
                    }
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

    private fun po(from: Event?, to: Event, inEdge: Boolean = false) {
        from ?: return
        pos.add(Relation(if (inEdge) RelationType.EPO else RelationType.PO, from, to))
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
        getOrPut(from.const.varDecl) { mutableListOf() }.add(Relation(type, from, to))

    private fun <T : Type> Expr<T>.withConsts(varToConst: Map<out Decl<*>, ConstDecl<*>>): Expr<T> {
        if (this is RefExpr<T>) {
            return (varToConst[decl]?.ref as? RefExpr<T>) ?: this
        }
        return map { it.withConsts(varToConst) }
    }

    private fun <T : Type> VarDecl<T>.getNewIndexed(increment: Boolean = true): IndexedConstDecl<T> {
        val constDecl = getConstDecl(indexing.get(this))
        if (increment) indexing = indexing.inc(this)
        return constDecl
    }

    fun printXcfa() = xcfa.toDot { edge ->
        "(${
            events.values.flatMap { it.flatMap { it.value } }.filter { it.edge == edge }
                .joinToString(",") { it.const.name }
        })"
    }

    // ~DPLL(OC)
    private lateinit var modifiableRels: List<Relation>

    private class DecisionPoint(
        val relation: Relation? = null,
        val event: Event? = null,
        val rels: Array<Array<Boolean>>
    ) {

        companion object {

            private fun initRels(rels: Array<Array<Boolean>>) =
                Array(rels.size) { i -> Array(rels.size) { j -> rels[i][j] } }
        }

        constructor(rels: Array<Array<Boolean>>, e: Event) : this(event = e, rels = initRels(rels))
        constructor(rels: Array<Array<Boolean>>, r: Relation) : this(relation = r, rels = initRels(rels))
    }

    private fun dpll() {
        modifiableRels = rfs.values.flatten() // modifiable relation vars
        val flatEvents = events.values.flatMap { it.values.flatten() }
        val initialRels = Array(flatEvents.size) { Array(flatEvents.size) { false } }
        pos.forEach { setAndClose(initialRels, it) }
        val decisionStack = Stack<DecisionPoint>()
        decisionStack.push(DecisionPoint(rels = initialRels)) // not really a decision point (initial)

        while (solver.check().isSat) {
            val valuation = solver.model.toMap()
            val changedRfs = modifiableRels.filter {
                val oldValue = it.value
                it.value(valuation) != oldValue
            }
            val changedEnabledEvents = flatEvents.filter {
                val oldValue = it.enabled
                it.type == EventType.WRITE && it.enabled(solver.model) != oldValue
            }

            // backtrack
            changedRfs.forEach { r -> decisionStack.popUntil { it.relation == r } }
            changedEnabledEvents.forEach { e -> decisionStack.popUntil { it.event == e } }

            // propagate
            changedRfs.filter { it.value == true }.forEach { rf ->
                val decision = DecisionPoint(decisionStack.peek().rels, rf)
                setAndClose(decision.rels, rf)
                decisionStack.push(decision)
                events[rf.from.const.varDecl]!!.values.flatten()
                    .filter { it.type == EventType.WRITE && it.id != rf.from.id }
                    .forEach { w -> derive(decision.rels, rf, w) }
            }
            changedEnabledEvents.forEach { w ->
                val decision = DecisionPoint(decisionStack.peek().rels, w)
                decisionStack.push(decision)
                rfs[w.const.varDecl]!!
                    .filter { it.from.id != w.id }
                    .forEach { rf -> derive(decision.rels, rf, w) }
            }
        }
    }

    private fun derive(rels: Array<Array<Boolean>>, rf: Relation, w: Event) {
        if (rels[w.id][rf.to.id]) {
            setAndClose(rels, w.id, rf.from.id) // WS derivation
        } else if (rels[rf.from.id][w.id]) {
            setAndClose(rels, rf.to.id, w.id) // FR derivation
        }
    }

    private fun setAndClose(rels: Array<Array<Boolean>>, rel: Relation) = setAndClose(rels, rel.from.id, rel.to.id)

    private fun setAndClose(rels: Array<Array<Boolean>>, from: Int, to: Int) {
        val toClose = mutableListOf(from to to)
        while (toClose.isNotEmpty()) {
            val (i1, i2) = toClose.first()
            toClose.removeFirst() // toClose.remove(i1 to i2)
            if (rels[i1][i2]) continue

            rels[i1][i2] = true
            rels[i2].forEachIndexed { i2next, b ->
                if (b && !rels[i1][i2next]) {
                    toClose.add(i1 to i2next)
                }
            }
            rels.forEachIndexed { i1previous, b ->
                if (b[i1] && !rels[i1previous][i2]) {
                    toClose.add(i1previous to i2)
                }
            }
        }
    }

    private fun <T> Stack<T>.popUntil(predicate: (T) -> Boolean) {
        val index = indexOfFirst(predicate)
        if (index > -1) while (size > index) pop()
    }
}
