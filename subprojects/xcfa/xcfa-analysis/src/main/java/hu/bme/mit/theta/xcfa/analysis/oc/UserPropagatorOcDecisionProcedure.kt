package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverFactory
import hu.bme.mit.theta.solver.javasmt.JavaSMTUserPropagator
import org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3
import java.util.*

internal class UserPropagatorOcDecisionProcedure : OcDecisionProcedure, JavaSMTUserPropagator() {

    private val partialAssignment = Stack<OcAssignment>()
    override val solver: Solver = JavaSMTSolverFactory.create(Z3, arrayOf()).createSolverWithPropagators(this)
    private var solverLevel: Int = 0

    private lateinit var writes: Map<VarDecl<*>, Map<Int, List<Event>>>
    private lateinit var flatWrites: List<Event>
    private lateinit var rfs: Map<VarDecl<*>, List<Relation>>
    private lateinit var flatRfs: List<Relation>

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<Event>>>,
        pos: List<Relation>,
        rfs: Map<VarDecl<*>, List<Relation>>,
    ): SolverStatus? {
        this.writes = events.keys.associateWith { v -> events[v]!!.keys.associateWith { p -> events[v]!![p]!!.filter { it.type == EventType.WRITE } } }
        flatWrites = this.writes.values.flatMap { it.values.flatten() }
        this.rfs = rfs
        flatRfs = rfs.values.flatten()

        val clkSize = events.values.flatMap { it.values.flatten() }.maxOf { it.clkId } + 1
        val initialRels = Array(clkSize) { Array<Reason?>(clkSize) { null } }
        pos.forEach { setAndClose(initialRels, it) }
        partialAssignment.push(OcAssignment(rels = initialRels))

        flatRfs.forEach { rf -> registerExpression(rf.declRef) }
        flatWrites.forEach { w -> if (w.guard.isNotEmpty()) registerExpression(w.guardExpr) }

        return solver.check()
    }

    override fun onKnownValue(expr: Expr<BoolType>, value: Boolean) {
        if (value) {
            flatRfs.find { it.declRef == expr }?.let { rf -> propagate(rf) }
                ?: flatWrites.filter { it.guardExpr == expr }.forEach { w -> propagate(w) }
        }
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

    private fun propagate(rf: Relation) {
        check(rf.type == RelationType.RFI || rf.type == RelationType.RFE)
        val assignement = OcAssignment(partialAssignment.peek().rels, rf, solverLevel)
        partialAssignment.push(assignement)
        val reason0 = setAndClose(assignement.rels, rf)
        if (reason0 != null) {
            propagateConflict(reason0.exprs)
        }

        val writes = writes[rf.from.const.varDecl]!!.values.flatten()
            .filter { w -> w.guard.isEmpty() || partialAssignment.any { it.event == w } }
        for (w in writes) {
            val reason = derive(assignement.rels, rf, w)
            if (reason != null) {
                propagateConflict(reason.exprs)
            }
        }
    }

    private fun propagate(w: Event) {
        check(w.type == EventType.WRITE)
        rfs[w.const.varDecl]?.filter { r -> partialAssignment.any { it.relation == r } }?.let { rfs ->
            val assignment = OcAssignment(partialAssignment.peek().rels, w, solverLevel)
            partialAssignment.push(assignment)
            for (rf in rfs) {
                val reason = derive(assignment.rels, rf, w)
                if (reason != null) {
                    propagateConflict(reason.exprs)
                }
            }
        }
    }
}