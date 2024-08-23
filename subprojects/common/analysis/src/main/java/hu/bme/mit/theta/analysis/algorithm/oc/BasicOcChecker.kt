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
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.SolverStatus
import java.util.*

class BasicOcChecker<E : Event> : OcCheckerBase<E>() {

    override val solver: Solver = SolverManager.resolveSolverFactory("Z3:4.13").createSolver()
    private var relations: Array<Array<Reason?>>? = null

    override fun check(
        events: Map<VarDecl<*>, Map<Int, List<E>>>,
        pos: List<Relation<E>>,
        rfs: Map<VarDecl<*>, Set<Relation<E>>>,
    ): SolverStatus? {
        val modifiableRels = rfs.values.flatten() // modifiable relation vars
        val flatEvents = events.values.flatMap { it.values.flatten() }
        val initialRels = Array(flatEvents.size) { Array<Reason?>(flatEvents.size) { null } }
        pos.forEach { setAndClose(initialRels, it) }
        val decisionStack = Stack<OcAssignment<E>>()
        decisionStack.push(OcAssignment(rels = initialRels)) // not really a decision point (initial)

        dpllLoop@
        while (solver.check().isSat) { // DPLL loop
            val valuation = solver.model.toMap()
            val changedRfs = modifiableRels.filter { rel ->
                val value = rel.enabled(valuation)
                decisionStack.popUntil({ it.relation == rel }, value) && value == true
            }
            val changedEnabledEvents = flatEvents.filter { ev ->
                val enabled = ev.enabled(solver.model)
                if (ev.type != EventType.WRITE || !rfs.containsKey(ev.const.varDecl)) return@filter false
                decisionStack.popUntil({ it.event == ev }, enabled) && enabled == true
            }

            // propagate
            for (rf in changedRfs) {
                val decision = OcAssignment(decisionStack.peek().rels, rf)
                decisionStack.push(decision)
                val reason0 = setAndClose(decision.rels, rf)
                if (propagate(reason0)) continue@dpllLoop

                val writes = events[rf.from.const.varDecl]!!.values.flatten()
                    .filter { it.type == EventType.WRITE && it.enabled == true }
                for (w in writes) {
                    val reason = derive(decision.rels, rf, w)
                    if (propagate(reason)) continue@dpllLoop
                }
            }

            for (w in changedEnabledEvents) {
                val decision = OcAssignment(decisionStack.peek().rels, w)
                decisionStack.push(decision)
                for (rf in rfs[w.const.varDecl]!!.filter { it.enabled == true }) {
                    val reason = derive(decision.rels, rf, w)
                    if (propagate(reason)) continue@dpllLoop
                }
            }

            relations = decisionStack.peek().rels
            return solver.status // no conflict found, counterexample is valid
        }

        relations = decisionStack.peek().rels
        return solver.status
    }

    override fun getRelations(): Array<Array<Reason?>>? = relations?.copy()

    override fun propagate(reason: Reason?): Boolean {
        reason ?: return false
        propagated.add(reason)
        solver.add(BoolExprs.Not(reason.expr))
        return true
    }

    /**
     *  Returns true if obj is not on the stack (in other words, if the value of obj is changed in the new model)
     */
    private fun <T> Stack<T>.popUntil(obj: (T) -> Boolean, value: Boolean?): Boolean {
        val index = indexOfFirst(obj)
        if (index == -1) return true
        if (value == true) return false
        while (size > index) pop()
        return true
    }
}