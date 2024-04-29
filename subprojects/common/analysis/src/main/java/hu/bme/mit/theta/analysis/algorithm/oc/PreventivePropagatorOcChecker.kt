package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.SolverStatus

class PreventivePropagatorOcChecker<E : Event> : UserPropagatorOcChecker<E>() {

    private lateinit var reads: Map<VarDecl<*>, List<E>>
    private val preventedClauses: MutableSet<Triple<Relation<E>, E, Reason>> = mutableSetOf()

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, List<Relation<E>>>,
    ): SolverStatus? {
        reads = events.keys.associateWith { v -> events[v]!!.values.flatten().filter { it.type == EventType.READ } }
        return super.check(events, pos, rfs)
    }

    override fun propagate(expr: Expr<BoolType>) {
        super.propagate(expr)
        preventivePropagation()
    }

    private fun preventivePropagation() {
        val rels = partialAssignment.peek().rels
        val preventiveClauses = mutableSetOf<Triple<Relation<E>, E, Reason>>() // rf{w->r}, w'
        writes.forEach { (v, ws) ->
            val rs = reads[v] ?: emptyList()
            for (w in ws) for (r in rs) {
                rels[r.clkId][w.clkId]?.let { reason -> // r -> w
                    rfs[v]?.find { it.from == w && it.to == r }?.let { rf -> // rf{w->r}
                        userPropagator.propagateConsequence(reason.exprs, Not(rf.declRef))
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
                propagated = userPropagator.propagateConsequence(reason.exprs + rf.declRef, Not(w.guardExpr))
            }
            if (partialAssignment.any { it.event == w }) {
                propagated = userPropagator.propagateConsequence(reason.exprs + w.guardExpr, Not(rf.declRef))
            }
            propagated != null
        })
    }
}