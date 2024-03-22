package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import java.util.*

internal class BasicOcDecisionProcedure : OcDecisionProcedure {

    override fun check(
        solver: Solver,
        events: MutableMap<VarDecl<*>, MutableMap<Int, MutableList<Event>>>,
        pos: MutableList<Relation>,
        rfs: MutableMap<VarDecl<*>, MutableList<Relation>>,
    ): SolverStatus? {
        val modifiableRels = rfs.values.flatten() // modifiable relation vars
        val flatEvents = events.values.flatMap { it.values.flatten() }
        val initialRels = Array(flatEvents.size) { Array<Reason?>(flatEvents.size) { null } }
        pos.forEach { setAndClose(initialRels, it) }
        val decisionStack = Stack<DecisionPoint>()
        decisionStack.push(DecisionPoint(rels = initialRels)) // not really a decision point (initial)

        dpllLoop@
        while (solver.check().isSat) { // DPLL loop
            val valuation = solver.model.toMap()
            val changedRfs = modifiableRels.filter { rel ->
                val value = rel.value(valuation)
                decisionStack.popUntil({ it.relation == rel }, value) && value == true
            }
            val changedEnabledEvents = flatEvents.filter { ev ->
                val enabled = ev.enabled(solver.model)
                if (ev.type != EventType.WRITE || !rfs.containsKey(ev.const.varDecl)) return@filter false
                decisionStack.popUntil({ it.event == ev }, enabled) && enabled == true
            }

            // propagate
            for (rf in changedRfs) {
                val decision = DecisionPoint(decisionStack.peek().rels, rf)
                decisionStack.push(decision)
                val reason0 = setAndClose(decision.rels, rf)
                if (reason0 != null) {
                    solver.add(BoolExprs.Not(reason0.expr))
                    continue@dpllLoop
                }

                val writes = events[rf.from.const.varDecl]!!.values.flatten()
                    .filter { it.type == EventType.WRITE && it.enabled == true }
                for (w in writes) {
                    val reason = derive(decision.rels, rf, w)
                    if (reason != null) {
                        solver.add(BoolExprs.Not(reason.expr))
                        continue@dpllLoop
                    }
                }
            }

            for (w in changedEnabledEvents) {
                val decision = DecisionPoint(decisionStack.peek().rels, w)
                decisionStack.push(decision)
                for (rf in rfs[w.const.varDecl]!!.filter { it.value == true }) {
                    val reason = derive(decision.rels, rf, w)
                    if (reason != null) {
                        solver.add(BoolExprs.Not(reason.expr))
                        continue@dpllLoop
                    }
                }
            }

            return solver.status // no conflict found, counterexample is valid
        }
        return solver.status
    }

    private fun derive(rels: Array<Array<Reason?>>, rf: Relation, w: Event): Reason? = when {
        rf.from.clkId == rf.to.clkId -> null // rf within an atomic block
        w.clkId == rf.from.clkId || w.clkId == rf.to.clkId -> null // w within an atomic block with one of the rf ends

        rels[w.clkId][rf.to.clkId] != null -> { // WS derivation
            val reason = WriteSerializationReason(rf, w, rels[w.clkId][rf.to.clkId]!!)
            setAndClose(rels, w.clkId, rf.from.clkId, reason)
        }

        rels[rf.from.clkId][w.clkId] != null -> { // FR derivation
            val reason = FromReadReason(rf, w, rels[rf.from.clkId][w.clkId]!!)
            setAndClose(rels, rf.to.clkId, w.clkId, reason)
        }

        else -> null
    }

    private fun setAndClose(rels: Array<Array<Reason?>>, rel: Relation): Reason? {
        if (rel.from.clkId == rel.to.clkId) return null // within an atomic block
        return setAndClose(rels, rel.from.clkId, rel.to.clkId, when (rel.type) {
            RelationType.PO, RelationType.EPO -> PoReason
            else -> RelationReason(rel)
        })
    }

    private fun setAndClose(rels: Array<Array<Reason?>>, from: Int, to: Int, reason: Reason): Reason? {
        if (from == to) return reason // cycle (self-loop) found
        val toClose = mutableListOf(from to to to reason)
        while (toClose.isNotEmpty()) {
            val (fromTo, r) = toClose.removeFirst()
            val (i1, i2) = fromTo
            check(i1 != i2)
            if (rels[i1][i2] != null) continue

            rels[i1][i2] = r
            rels[i2].forEachIndexed { i2next, b ->
                if (b != null && rels[i1][i2next] == null) { // i2 -> i2next, not i1 -> i2next
                    val combinedReason = r and b
                    if (i1 == i2next) return combinedReason // cycle (self-loop) found
                    toClose.add(i1 to i2next to combinedReason)
                }
            }
            rels.forEachIndexed { i1previous, b ->
                if (b[i1] != null && rels[i1previous][i2] == null) { // i1previous -> i1, not i1previous -> i2
                    val combinedReason = r and b[i1]!!
                    if (i1previous == i2) return combinedReason // cycle (self-loop) found
                    toClose.add(i1previous to i2 to combinedReason)
                }
            }
        }
        return null
    }

    /**
     *  Returns true if obj is not on the stack (in other words, if the value of obj is changed in the new model)
     */
    private fun <T> Stack<T>.popUntil(obj: (T) -> Boolean, value: Boolean?): Boolean {
        val index = indexOfFirst(obj)
        if (index == -1) return true
        if (value == true) return false
        while (size > index) pop()
        return true
    }
}