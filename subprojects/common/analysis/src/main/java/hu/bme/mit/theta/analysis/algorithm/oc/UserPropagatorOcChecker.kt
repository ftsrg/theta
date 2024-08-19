/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.oc

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverFactory
import hu.bme.mit.theta.solver.javasmt.JavaSMTUserPropagator
import org.sosy_lab.java_smt.SolverContextFactory.Solvers.Z3
import java.util.*

open class UserPropagatorOcChecker<E : Event> : OcCheckerBase<E>() {

    protected val partialAssignment = Stack<OcAssignment<E>>()
    protected lateinit var writes: Map<VarDecl<*>, List<E>>
    protected lateinit var flatWrites: List<E>
    protected lateinit var rfs: Map<VarDecl<*>, Set<Relation<E>>>
    private lateinit var flatRfs: List<Relation<E>>

    protected val userPropagator: JavaSMTUserPropagator = object : JavaSMTUserPropagator() {
        override fun onKnownValue(expr: Expr<BoolType>, value: Boolean) {
            if (value) propagate(expr)
        }

        override fun onFinalCheck() =
            flatWrites.filter { w -> w.guard.isEmpty() || partialAssignment.any { it.event == w } }.forEach { w ->
                propagate(w)
            }

        override fun onPush() {
            solverLevel++
        }

        override fun onPop(levels: Int) = pop(levels)
    }

    override val solver: Solver = JavaSMTSolverFactory.create(Z3, arrayOf()).createSolverWithPropagators(userPropagator)
    protected var solverLevel: Int = 0

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    ): SolverStatus? {
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

    protected open fun propagate(expr: Expr<BoolType>) {
        flatRfs.find { it.declRef == expr }?.let { rf -> propagate(rf) }
            ?: flatWrites.filter { it.guardExpr == expr }.forEach { w -> propagate(w) }
    }

    private fun propagate(rf: Relation<E>) {
        check(rf.type == RelationType.RF)
        val assignment = OcAssignment(partialAssignment.peek().rels, rf, solverLevel)
        partialAssignment.push(assignment)
        val reason0 = setAndClose(assignment.rels, rf)
        propagate(reason0)

        val writes = writes[rf.from.const.varDecl]!!
            .filter { w -> w.guard.isEmpty() || partialAssignment.any { it.event == w } }
        for (w in writes) {
            val reason = derive(assignment.rels, rf, w)
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

    protected open fun pop(levels: Int) {
        solverLevel -= levels
        while (partialAssignment.isNotEmpty() && partialAssignment.peek().solverLevel > solverLevel) {
            partialAssignment.pop()
        }
    }
}