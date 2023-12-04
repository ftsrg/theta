/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.analysis.pointers

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.DerefWriteStmt
import hu.bme.mit.theta.core.type.anytype.AddrOfExpr
import hu.bme.mit.theta.core.type.anytype.DeRefExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.core.utils.PointerStore
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA

interface PointerAction {

    val p: VarDecl<*>
    val q: VarDecl<*>
}

data class ReferencingPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DereferencingReadPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DereferencingWritePointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class AliasingPointerAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction
data class DoubleDerefAliasAction(override val p: VarDecl<*>, override val q: VarDecl<*>) : PointerAction

abstract class PointerAnalysis {

    abstract fun run(xcfa: XCFA): PointerStore
    abstract fun runOnActions(actions: List<PointerAction>): PointerStore

    companion object {

        private fun getPointerAction(label: StmtLabel): PointerAction? {
            try {
                if (label.stmt is AssignStmt<*>) {
                    val assignStmt = label.stmt as AssignStmt<*>
                    val expr = assignStmt.expr

                    if (expr is AddrOfExpr<*>) {
                        // p = &i
                        val pVarDecl = assignStmt.varDecl
                        val iVarDecl = ((expr.op as RefExpr<*>).decl) as VarDecl<*>
                        return ReferencingPointerAction(pVarDecl, iVarDecl)
                    } else if (expr is DeRefExpr<*> || (expr is IntModExpr && (expr as IntModExpr).leftOp is DeRefExpr<*>)) {
                        // p = *q
                        val pVarDecl = assignStmt.varDecl
                        val qVarDecl = if (expr is DeRefExpr<*>) {
                            (expr.op as RefExpr<*>).decl as VarDecl<*>
                        } else {
                            (((expr as IntModExpr).leftOp as DeRefExpr<*>).op as RefExpr<*>).decl as VarDecl<*>
                        }
                        return DereferencingReadPointerAction(pVarDecl, qVarDecl)
                    } else if (expr is RefExpr<*>) {
                        // p = q
                        val pVarDecl = assignStmt.varDecl
                        val qVarDecl = expr.decl as VarDecl<*>

                        return AliasingPointerAction(pVarDecl, qVarDecl)
                    }
                } else if (label.stmt is DerefWriteStmt) {
                    // *p = q or *p = *q
                    val pVarDecl = ((label.stmt as DerefWriteStmt).deRef.op as RefExpr<*>).decl as VarDecl<*>
                    return if ((label.stmt as DerefWriteStmt).expr is RefExpr<*>) {
                        val qVarDecl = ((label.stmt as DerefWriteStmt).expr as RefExpr<*>).decl as VarDecl<*>
                        DereferencingWritePointerAction(pVarDecl, qVarDecl)
                    } else if ((label.stmt as DerefWriteStmt).expr is DeRefExpr<*>) {
                        val qVarDecl = (((label.stmt as DerefWriteStmt).expr as DeRefExpr<*>).op as RefExpr<*>).decl as VarDecl<*>
                        DoubleDerefAliasAction(pVarDecl, qVarDecl)
                    } else {
                        null
                    }
                }
            } catch (e: Exception) {
                println("Exception in getPointerAction: $label ${e.message}")
                return null
            }
            return null
        }

        @JvmStatic
        protected fun getPointerActions(xcfa: XCFA): List<PointerAction> {
            val actions = mutableListOf<PointerAction>()
            xcfa.procedures.forEach { procedure ->
                val edges = procedure.edges
                edges.forEach { edge ->
                    val labels = edge.label.getFlatLabels()
                    labels.forEach { label ->
                        if (label is StmtLabel) {
                            val action = getPointerAction(label)
                            if (action != null) {
                                actions.add(action)
                            }
                        }
                    }
                }
            }
            return actions
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
                    // throw UnsupportedOperationException("DereferencingWritePointerAction found")
                    println("DereferencingWritePointerAction found: $label")
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

                is DoubleDerefAliasAction -> {
                    // *p = *q
                    newPointerStore.pointsTo(action.p).forEach { newPointerStore.removePointsToAny(it) }
                    newPointerStore.pointsTo(action.p).forEach { r ->
                        newPointerStore.pointsTo(action.q).forEach { s ->
                            newPointerStore.pointsTo(s).forEach { t ->
                                newPointerStore.addPointsTo(r, t)
                            }
                        }
                    }
                }
            }
            return newPointerStore
        }
    }
}