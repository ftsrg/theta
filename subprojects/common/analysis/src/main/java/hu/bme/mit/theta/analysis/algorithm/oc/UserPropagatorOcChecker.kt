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

class UserPropagatorOcChecker<E : Event> : OcCheckerBase<E>, JavaSMTUserPropagator() {

    private val partialAssignment = Stack<OcAssignment<E>>()
    override val solver: Solver = JavaSMTSolverFactory.create(Z3, arrayOf()).createSolverWithPropagators(this)
    private var solverLevel: Int = 0

    private lateinit var writes: Map<VarDecl<*>, Map<Int, List<E>>>
    private lateinit var flatWrites: List<E>
    private lateinit var rfs: Map<VarDecl<*>, List<Relation<E>>>
    private lateinit var flatRfs: List<Relation<E>>

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, List<Relation<E>>>,
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

    override fun getRelations(): Array<Array<Reason?>>? = partialAssignment.lastOrNull()?.rels?.copy()

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

    private fun propagate(rf: Relation<E>) {
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

    private fun propagate(w: E) {
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