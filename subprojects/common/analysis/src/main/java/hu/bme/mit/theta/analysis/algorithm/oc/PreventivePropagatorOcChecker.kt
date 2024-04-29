package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverFactory
import hu.bme.mit.theta.solver.javasmt.JavaSMTUserPropagator
import org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3
import java.util.*

class PreventivePropagatorOcChecker<E : Event> : OcCheckerBase<E>() {

    private val partialAssignment = Stack<OcAssignment<E>>()
    private lateinit var reads: Map<VarDecl<*>, List<E>>
    private lateinit var writes: Map<VarDecl<*>, List<E>>
    private lateinit var flatWrites: List<E>
    private lateinit var rfs: Map<VarDecl<*>, List<Relation<E>>>
    private lateinit var flatRfs: List<Relation<E>>

    private val preventedClauses: MutableSet<Triple<Relation<E>, E, Reason>> = mutableSetOf()

    private val userPropagator: JavaSMTUserPropagator = object : JavaSMTUserPropagator() {
        override fun onKnownValue(expr: Expr<BoolType>, value: Boolean) {
            if (!value) return

            flatRfs.find { it.declRef == expr }?.let { rf -> propagate(rf) }
                ?: flatWrites.filter { it.guardExpr == expr }.forEach { w -> propagate(w) }

            val rels = partialAssignment.peek().rels
            val preventiveClauses = mutableSetOf<Triple<Relation<E>, E, Reason>>() // rf{w->r}, w'
            writes.forEach { (v, ws) ->
                val rs = reads[v] ?: emptyList()
                for (w in ws) for (r in rs) {
                    rels[r.clkId][w.clkId]?.let { reason -> // r -> w
                        rfs[v]?.find { it.from == w && it.to == r }?.let { rf -> // rf{w->r}
                            propagateConsequence(reason.exprs, Not(rf.declRef))
                        }
                    }
                    rels[w.clkId][r.clkId]?.let { wrReason ->
                        for (w0 in ws)
                            rels[w0.clkId][w.clkId]?.let { w0wReason -> // w0 -> w -> r
                                rfs[v]?.find { it.from == w0 && it.to == r }?.let { rf -> // rf{w0->r}
                                    Triple(rf, w, wrReason and w0wReason).let {
                                        if (it !in preventedClauses) preventiveClauses.add(it)
                                    }
                                }
                            }
                    }
                }
            }

            preventedClauses.addAll(preventiveClauses.filter { (rf, w, reason) ->
                var propagated: Unit? = null
                if (partialAssignment.any { it.relation == rf }) {
                    propagated = propagateConsequence(reason.exprs + rf.declRef, Not(w.guardExpr))
                }
                if (partialAssignment.any { it.event == w }) {
                    propagated = propagateConsequence(reason.exprs + w.guardExpr, Not(rf.declRef))
                }
                propagated != null
            })
        }

        override fun onFinalCheck() =
            flatWrites.filter { w -> w.guard.isEmpty() || partialAssignment.any { it.event == w } }.forEach { w ->
                propagate(w)
            }

        override fun onPush() {
            solverLevel++
        }

        override fun onPop(levels: Int) {
            solverLevel -= levels
            while (partialAssignment.isNotEmpty() && partialAssignment.peek().solverLevel > solverLevel) {
                partialAssignment.pop()
            }
        }
    }

    override val solver: Solver = JavaSMTSolverFactory.create(Z3, arrayOf()).createSolverWithPropagators(userPropagator)
    private var solverLevel: Int = 0

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, List<Relation<E>>>,
    ): SolverStatus? {
        reads = events.keys.associateWith { v -> events[v]!!.values.flatten().filter { it.type == EventType.READ } }
        writes = events.keys.associateWith { v -> events[v]!!.values.flatten().filter { it.type == EventType.WRITE } }
        flatWrites = this.writes.values.flatten()
        this.rfs = rfs
        flatRfs = rfs.values.flatten()

        val clkSize = events.values.flatMap { it.values.flatten() }.maxOf { it.clkId } + 1
        val initialRels = Array(clkSize) { Array<Reason?>(clkSize) { null } }
        pos.forEach { setAndClose(initialRels, it) }
        partialAssignment.push(OcAssignment(rels = initialRels))

        flatRfs.forEach { rf -> userPropagator.registerExpression(rf.declRef) }
        flatWrites.forEach { w -> if (w.guard.isNotEmpty()) userPropagator.registerExpression(w.guardExpr) }

        return solver.check()
    }

    override fun getRelations(): Array<Array<Reason?>>? = partialAssignment.lastOrNull()?.rels?.copy()

    private fun propagate(rf: Relation<E>) {
        check(rf.type == RelationType.RFI || rf.type == RelationType.RFE)
        val assignement = OcAssignment(partialAssignment.peek().rels, rf, solverLevel)
        partialAssignment.push(assignement)
        val reason0 = setAndClose(assignement.rels, rf)
        propagate(reason0)

        val writes = writes[rf.from.const.varDecl]!!
            .filter { w -> w.guard.isEmpty() || partialAssignment.any { it.event == w } }
        for (w in writes) {
            val reason = derive(assignement.rels, rf, w)
            propagate(reason)
        }
    }

    private fun propagate(w: E) {
        check(w.type == EventType.WRITE)
        rfs[w.const.varDecl]?.filter { r -> partialAssignment.any { it.relation == r } }?.let { rfs ->
            val assignment = OcAssignment(partialAssignment.peek().rels, w, solverLevel)
            partialAssignment.push(assignment)
            for (rf in rfs) {
                val reason = derive(assignment.rels, rf, w)
                propagate(reason)
            }
        }
    }

    override fun propagate(reason: Reason?): Boolean {
        reason ?: return false
        propagated.add(reason)
        userPropagator.propagateConflict(reason.exprs)
        return true
    }
}