package hu.bme.mit.theta.xcfa.analysis.pointers

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.DerefWriteStmt
import hu.bme.mit.theta.core.type.anytype.AddrOfExpr
import hu.bme.mit.theta.core.type.anytype.DeRefExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.utils.PointerStore
import hu.bme.mit.theta.xcfa.model.StmtLabel

interface PointerAction {
    val p: VarDecl<*>
    val q: VarDecl<*>
}

data class ReferencingPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DereferencingReadPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DereferencingWritePointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class AliasingPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction

abstract class PointerAnalysis {
    abstract fun runOnActions(actions: List<PointerAction>): PointerStore

    companion object {
        fun getPointerAction(label: StmtLabel): PointerAction? {
            if (label.stmt is AssignStmt<*>) {
                val assignStmt = label.stmt as AssignStmt<*>
                val expr = assignStmt.expr

                if (expr is AddrOfExpr<*>) {
                    // p = &i
                    val pVarDecl = assignStmt.varDecl
                    val iVarDecl = ((expr.op as RefExpr<*>).decl) as VarDecl<*>
                    return ReferencingPointerAction(pVarDecl, iVarDecl)
                } else if (expr is DeRefExpr<*>) {
                    // p = *q
                    val pVarDecl = assignStmt.varDecl
                    val qVarDecl = (expr.op as RefExpr<*>).decl as VarDecl<*>

                    return DereferencingReadPointerAction(pVarDecl, qVarDecl)
                } else if (expr is RefExpr<*>) {
                    // p = q
                    val pVarDecl = assignStmt.varDecl
                    val qVarDecl = expr.decl as VarDecl<*>

                    return AliasingPointerAction(pVarDecl, qVarDecl)
                }
            } else if (label.stmt is DerefWriteStmt) {
                // *p = q
                val pVarDecl = ((label.stmt as DerefWriteStmt).deRef.op as RefExpr<*>).decl as VarDecl<*>
                val qVarDecl = ((label.stmt as DerefWriteStmt).expr as RefExpr<*>).decl as VarDecl<*>

                return DereferencingWritePointerAction(pVarDecl, qVarDecl)
            }
            return null
        }

        fun updateWithLabel(label: StmtLabel, pointerStore: PointerStore): PointerStore {
            val newPointerStore = pointerStore.copy()
            when (val action = getPointerAction(label)) {
                is ReferencingPointerAction -> {
                    // p = &q
                    newPointerStore.removePointsToAny(action.p)
                    newPointerStore.addPointsTo(action.p, action.q)
                }
                is DereferencingWritePointerAction -> {
                    // *p = q
                    throw UnsupportedOperationException("DereferencingWritePointerAction found")
                }
                is DereferencingReadPointerAction -> {
                    // p = *q
                    newPointerStore.removePointsToAny(action.p)
                    newPointerStore.pointsTo(action.q).forEach { q ->
                        newPointerStore.pointsTo(q).forEach { r ->
                            newPointerStore.addPointsTo(action.p, r)
                        }
                    }
                }
                is AliasingPointerAction -> {
                    // p = q
                    newPointerStore.removePointsToAny(action.p)
                    newPointerStore.pointsTo(action.q).forEach { q ->
                        newPointerStore.addPointsTo(action.p, q)
                    }
                }
            }
            return newPointerStore
        }
    }
}