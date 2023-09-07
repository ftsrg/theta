package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.analysis.por.extension
import hu.bme.mit.theta.xcfa.analysis.por.nullableExtension
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import kotlin.math.min

lateinit var COI: ConeOfInfluence

private typealias S = XcfaState<out ExprState>
private typealias A = XcfaAction

class ConeOfInfluence(private val xcfa: XCFA) {

    var coreLts: LTS<S, A> = getXcfaLts()
    lateinit var coreTransFunc: TransFunc<S, A, XcfaPrec<out Prec>>

    private var lastPrec: Prec? = null

    private val startThreads: MutableSet<XcfaEdge> = mutableSetOf()
    private val edgeToProcedure: MutableMap<XcfaEdge, XcfaProcedure> = mutableMapOf()
    private var XcfaEdge.procedure: XcfaProcedure
        get() = edgeToProcedure[this]!!
        set(value) {
            edgeToProcedure[this] = value
        }
    private var XcfaLocation.scc: Int by extension()

    private val directObservers: MutableMap<XcfaEdge, MutableSet<XcfaEdge>> = mutableMapOf()
    private val interProcessObservers: MutableMap<XcfaEdge, MutableSet<XcfaEdge>> = mutableMapOf()

    private var XcfaAction.transFuncVersion: XcfaAction? by nullableExtension()

    data class ProcedureEntry(
        val procedure: XcfaProcedure,
        val scc: Int,
        val pid: Int
    )

    val lts = object : LTS<S, A> {
        override fun getEnabledActionsFor(state: S): Collection<A> {
            val enabled = coreLts.getEnabledActionsFor(state)
            return lastPrec?.let { replaceIrrelevantActions(state, enabled, it) } ?: enabled
        }

        override fun <P : Prec> getEnabledActionsFor(state: S, explored: Collection<A>, prec: P): Collection<A> {
            if (lastPrec != prec) reinitialize(prec)
            val enabled = coreLts.getEnabledActionsFor(state, explored, prec)
            return replaceIrrelevantActions(state, enabled, prec)
        }

        private fun replaceIrrelevantActions(state: S, enabled: Collection<A>, prec: Prec): Collection<A> {
            val procedures = state.processes.map { (pid, pState) ->
                val loc = pState.locs.peek()
                val procedure = loc.incomingEdges.ifEmpty(loc::outgoingEdges).first().procedure
                ProcedureEntry(procedure, loc.scc, pid)
            }.toMutableSet()

            do {
                var anyNew = false
                startThreads.filter { edge ->
                    procedures.any { edge.procedure == it.procedure && it.scc >= edge.source.scc }
                }.forEach { edge ->
                    edge.getFlatLabels().filterIsInstance<StartLabel>().forEach { startLabel ->
                        val procedure = xcfa.procedures.find { it.name == startLabel.name }!!
                        val procedureEntry = ProcedureEntry(procedure, procedure.initLoc.scc, -1)
                        if (procedureEntry !in procedures) {
                            procedures.add(procedureEntry)
                            anyNew = true
                        }
                    }
                }
            } while (anyNew)

            return enabled.map { action ->
                if (!isObserved(action, procedures)) {
                    replace(action, prec)
                } else {
                    action
                }
            }
        }

        private fun isObserved(action: A, procedures: MutableSet<ProcedureEntry>): Boolean {
            val toVisit = edgeToProcedure.keys.filter {
                it.source == action.edge.source && it.target == action.edge.target
            }.toMutableList()
            val visited = mutableSetOf<XcfaEdge>()

            while (toVisit.isNotEmpty()) {
                val visiting = toVisit.removeFirst()
                if (isRealObserver(visiting)) return true

                visited.add(visiting)
                val toAdd = (directObservers[visiting] ?: emptySet()) union
                    (interProcessObservers[visiting]?.filter { edge ->
                        procedures.any {
                            it.procedure == edge.procedure && it.scc >= edge.source.scc
                        } // the edge is still reachable
                    } ?: emptySet())
                toVisit.addAll(toAdd.filter { it !in visited })
            }
            return false
        }

        private fun replace(action: A, prec: Prec): XcfaAction {
            val replacedLabel = action.label.replace(prec)
            val newAction = action.withLabel(replacedLabel.first.wrapInSequenceLabel())
            newAction.transFuncVersion = action.withLabel(replacedLabel.second.wrapInSequenceLabel())
            return newAction
        }

        private fun XcfaLabel.replace(prec: Prec): Pair<XcfaLabel, XcfaLabel> = when (this) {
            is SequenceLabel -> pairOf(labels.map { it.replace(prec) }) { SequenceLabel(it, metadata) }
            is NondetLabel -> pairOf(labels.map { it.replace(prec) }) { NondetLabel(it.toSet(), metadata) }
            is StmtLabel -> {
                when (val stmt = this.stmt) {
                    is AssignStmt<*> -> if (stmt.varDecl in prec.usedVars) {
                        Pair(NopLabel, NopLabel)
                    } else {
                        Pair(this, NopLabel)
                    }

                    is HavocStmt<*> -> if (stmt.varDecl in prec.usedVars) {
                        Pair(NopLabel, NopLabel)
                    } else {
                        Pair(this, NopLabel)
                    }

                    else -> Pair(this, this)
                }
            }

            else -> Pair(this, this)
        }

        private inline fun <T> pairOf(list: List<Pair<T, T>>, builder: (List<T>) -> T): Pair<T, T> {
            return Pair(builder(list.map { it.first }), builder(list.map { it.second }))
        }

        private fun XcfaLabel.wrapInSequenceLabel(): SequenceLabel =
            if (this !is SequenceLabel) SequenceLabel(listOf(this)) else this
    }

    val transFunc = TransFunc<S, A, XcfaPrec<out Prec>> { state, action, prec ->
        coreTransFunc.getSuccStates(state, action.transFuncVersion ?: action, prec)
    }

    init {
        xcfa.procedures.forEach { tarjan(it.initLoc) }
    }

    fun reinitialize(prec: Prec) {
        directObservers.clear()
        interProcessObservers.clear()
        xcfa.procedures.forEach { procedure ->
            procedure.edges.forEach { edge ->
                edge.procedure = procedure
                if (edge.getFlatLabels().any { it is StartLabel }) startThreads.add(edge)
                findDirectObservers(edge, prec)
                findInterProcessObservers(edge, prec)
            }
        }
        lastPrec = prec

//        System.err.println("Direct:")
//        directObservers.forEach { (k, v) -> System.err.println("${k.label} -> ${v.map { it.label }}") }
//        System.err.println("Indirect:")
//        interProcessObservers.forEach { (k, v) -> System.err.println("${k.label} -> ${v.map { it.label }}") }
    }


    private fun tarjan(initLoc: XcfaLocation) {
        var sccCnt = 0
        var discCnt = 0
        val disc = mutableMapOf<XcfaLocation, Int>()
        val lowest = mutableMapOf<XcfaLocation, Int>()
        val visited = mutableSetOf<XcfaLocation>()
        val stack = Stack<XcfaLocation>()
        val toVisit = Stack<XcfaLocation>()
        toVisit.push(initLoc)

        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.peek()
            if (visiting !in visited) {
                disc[visiting] = discCnt++
                lowest[visiting] = disc[visiting]!!
                stack.push(visiting)
                visited.add(visiting)
            }

            for (edge in visiting.outgoingEdges) {
                if (edge.target in stack) {
                    lowest[visiting] = min(lowest[visiting]!!, lowest[edge.target]!!)
                } else if (edge.target !in visited) {
                    toVisit.push(edge.target)
                    break
                }
            }

            if (toVisit.peek() != visiting) continue

            if (lowest[visiting] == disc[visiting]) {
                val scc = sccCnt++
                while (stack.peek() != visiting) {
                    stack.pop().scc = scc
                }
                stack.pop().scc = scc // visiting
            }

            toVisit.pop()
        }
    }


    private fun isRealObserver(edge: XcfaEdge) = edge.label.collectAssumesVars().isNotEmpty()

    private fun findDirectObservers(edge: XcfaEdge, prec: Prec) {
        val precVars = prec.usedVars
        val writtenVars = edge.getVars().filter { it.value.isWritten && it.key in precVars }
        if (writtenVars.isEmpty()) return

        val toVisit = mutableListOf(edge)
        val visited = mutableSetOf<XcfaEdge>()
        while (toVisit.isNotEmpty()) {
            val visiting = toVisit.removeFirst()
            visited.add(visiting)
            addEdgeIfObserved(edge, visiting, writtenVars, precVars, directObservers)
            toVisit.addAll(visiting.target.outgoingEdges.filter { it !in visited })
        }
    }

    private fun findInterProcessObservers(edge: XcfaEdge, prec: Prec) {
        val precVars = prec.usedVars
        val writtenVars = edge.getVars().filter { it.value.isWritten && it.key in precVars }
        if (writtenVars.isEmpty()) return

        xcfa.procedures.forEach { procedure ->
            procedure.edges.forEach {
                addEdgeIfObserved(edge, it, writtenVars, precVars, interProcessObservers)
            }
        }
    }

    private fun addEdgeIfObserved(
        source: XcfaEdge, target: XcfaEdge, observableVars: Map<VarDecl<*>, AccessType>,
        precVars: Collection<VarDecl<*>>, relation: MutableMap<XcfaEdge, MutableSet<XcfaEdge>>
    ) {
        val vars = target.getVars()
        var relevantAction = vars.any { it.value.isWritten && it.key in precVars }
        if (!relevantAction) {
            val assumeVars = target.label.collectAssumesVars()
            relevantAction = assumeVars.any { it in precVars }
        }

        if (relevantAction && vars.any { it.key in observableVars && it.value.isRead }) {
            relation[source] = relation[source] ?: mutableSetOf()
            relation[source]!!.add(target)
        }
    }

}