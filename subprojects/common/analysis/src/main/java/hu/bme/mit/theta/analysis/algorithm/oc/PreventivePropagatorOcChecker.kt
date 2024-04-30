package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.SolverStatus

class PreventivePropagatorOcChecker<E : Event> : UserPropagatorOcChecker<E>() {

    private lateinit var reads: Map<VarDecl<*>, List<E>>
    private val preventedClauses: MutableMap<Int, MutableSet<Expr<BoolType>>> = mutableMapOf()

    private val Expr<BoolType>.prevented: Boolean get() = preventedClauses.any { this in it.value }

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    ): SolverStatus? {
        reads = events.keys.associateWith { v -> events[v]!!.values.flatten().filter { it.type == EventType.READ } }
        return super.check(events, pos, rfs)
    }

    override fun propagate(expr: Expr<BoolType>) {
        super.propagate(expr)
        preventivePropagation()
    }

    override fun pop(levels: Int) {
        super.pop(levels)
        preventedClauses.keys.filter { it > solverLevel }.forEach { preventedClauses.remove(it) }
    }

    private fun preventivePropagation() {
        val rels = partialAssignment.peek().rels
        writes.forEach { (v, ws) ->
            val rs = reads[v] ?: emptyList()
            for (w in ws) for (r in rs) {
                rels[r.clkId][w.clkId]?.let { reason -> // r -> w
                    rfs[v]?.find { it.from == w && it.to == r }?.let { rf -> // rf{w->r}
                        if (!rf.declRef.prevented) {
                            propagateUnit(reason, Not(rf.declRef))
                            preventedClauses.getOrPut(solverLevel) { mutableSetOf() }.add(rf.declRef)
                        }
                    }
                }
                rels[w.clkId][r.clkId]?.let { wrReason ->
                    for (w0 in ws)
                        rels[w0.clkId][w.clkId]?.let { w0wReason -> // w0 -> w -> r
                            rfs[v]?.find { it.from == w0 && it.to == r }?.let { rf -> // rf{w0->r}
                                val reason = wrReason and w0wReason
                                if (partialAssignment.any { it.relation == rf } && !w.guardExpr.prevented) {
                                    propagateUnit(reason, Not(w.guardExpr))
                                    preventedClauses.getOrPut(solverLevel) { mutableSetOf() }.add(w.guardExpr)
                                }
                                if (partialAssignment.any { it.event == w } && !rf.declRef.prevented) {
                                    propagateUnit(reason, Not(rf.declRef))
                                    preventedClauses.getOrPut(solverLevel) { mutableSetOf() }.add(rf.declRef)
                                }
                            }
                        }
                }
            }
        }
    }

    private fun propagateUnit(reason: Reason, consequence: Expr<BoolType>) =
        userPropagator.propagateConsequence(reason.exprs.filter { it != True() }, consequence)
}