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

    private lateinit var events: Map<VarDecl<*>, Map<Int, List<Event>>>
    private lateinit var flatEvents: List<Event>
    private lateinit var rfs: Map<VarDecl<*>, List<Relation>>
    private lateinit var flatRfs: List<Relation>

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<Event>>>,
        pos: List<Relation>,
        rfs: Map<VarDecl<*>, List<Relation>>,
    ): SolverStatus? {
        this.events = events.keys.associateWith { v -> events[v]!!.keys.associateWith { p -> events[v]!![p]!!.filter { it.type == EventType.WRITE } } }
        flatEvents = this.events.values.flatMap { it.values.flatten() }
        this.rfs = rfs
        flatRfs = rfs.values.flatten()

        val clkSize = events.values.flatMap { it.values.flatten() }.maxOf { it.clkId } + 1
        val initialRels = Array(clkSize) { Array<Reason?>(clkSize) { null } }
        pos.forEach { setAndClose(initialRels, it) }
        partialAssignment.push(OcAssignment(rels = initialRels))

        flatRfs.forEach { rf -> registerExpression(rf.declRef) }
        flatEvents.forEach { w -> registerExpression(w.guardExpr) }

        return solver.check()
    }

    override fun onKnownValue(expr: Expr<BoolType>, value: Boolean) {
        flatRfs.find { it.declRef == expr }?.let { rf ->
            if (value) {
                val assignement = OcAssignment(partialAssignment.peek().rels, rf, solverLevel)
                partialAssignment.push(assignement)
                val reason0 = setAndClose(assignement.rels, rf)
                if (reason0 != null) {
                    propagateConflict(reason0.exprs)
                }

                val writes = events[rf.from.const.varDecl]!!.values.flatten()
                    .filter { w -> partialAssignment.any { it.event == w } }
                for (w in writes) {
                    val reason = derive(assignement.rels, rf, w)
                    if (reason != null) {
                        propagateConflict(reason.exprs)
                    }
                }
            }
        } ?: flatEvents.filter { it.guardExpr == expr }.forEach { w ->
            if (value) {
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