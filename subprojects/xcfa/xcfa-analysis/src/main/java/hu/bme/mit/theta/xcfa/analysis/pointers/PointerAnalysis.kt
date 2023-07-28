package hu.bme.mit.theta.xcfa.analysis.pointers

import hu.bme.mit.theta.common.pointerstore.PointerStore
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Dereference
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.XCFA

interface PointerAction {
    val p: VarDecl<*>
    val q: VarDecl<*>
}

data class ReferencingPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DereferencingReadPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DereferencingWritePointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class AliasingPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction

abstract class PointerAnalysis {
    abstract fun run(xcfa: XCFA): PointerStore<VarDecl<*>>

    protected fun getPointerActions(xcfa: XCFA): List<PointerAction> {
        val main = xcfa.initProcedures.first().first
        val edges = main.edges
        val actions = mutableListOf<PointerAction>()
        edges.forEach { edge ->
            val labels = edge.label.getFlatLabels()
            labels.forEach { label ->
                val stmt = label.toStmt()
                if (stmt is AssignStmt<*>) {
                    val assignStmt = stmt as AssignStmt<*>
                    val expr = assignStmt.expr

                    if (expr is Reference<*, *>) {
                        // p = &i
                        val pVarDecl = assignStmt.varDecl
                        val iVarDecl = ((expr.op as RefExpr<*>).decl) as VarDecl<*>
                        actions.add(ReferencingPointerAction(pVarDecl, iVarDecl))
                    }
                    if (expr is ArrayWriteExpr<*, *> && expr.array is RefExpr<*>) {
                        // *p = q
                        val pVarDecl = (expr.index as RefExpr<*>).decl as VarDecl<*>
                        val qVarDecl = (expr.elem as RefExpr<*>).decl as VarDecl<*>

                        actions.add(DereferencingWritePointerAction(pVarDecl, qVarDecl))
                    }
                    if (expr is IntModExpr && expr.leftOp is Dereference<*, *>) {
                        // p = *q
                        val leftOp = expr.leftOp as Dereference<*, *>
                        val op = leftOp.op as RefExpr<*>
                        val pVarDecl = assignStmt.varDecl
                        val qVarDecl = op.decl as VarDecl<*>

                        actions.add(DereferencingReadPointerAction(pVarDecl, qVarDecl))
                    }
                    if (expr is RefExpr<*>) {
                        // p = q
                        val pVarDecl = assignStmt.varDecl
                        val qVarDecl = expr.decl as VarDecl<*>

                        actions.add(AliasingPointerAction(pVarDecl, qVarDecl))
                    }
                }
            }
        }
        return actions
    }
}