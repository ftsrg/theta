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

package hu.bme.mit.theta.analysis.algorithm.mcm.analysis

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.mcm.interpreter.MemoryEventProvider
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.common.Tuple
import hu.bme.mit.theta.common.Tuple1
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.graphsolver.compilers.GraphPatternCompiler
import hu.bme.mit.theta.graphsolver.patterns.constraints.GraphConstraint
import hu.bme.mit.theta.graphsolver.solvers.GraphSolver
import java.util.*

class FiniteStateChecker<S : ExplState, A : StmtAction, T>(
    private val mcm: Collection<GraphConstraint>,
    private val initFunc: InitFunc<S, ExplPrec>,
    private val actionFunc: LTS<S, A>,
    private val transFunc: TransFunc<S, A, ExplPrec>,
    private val memoryEventProvider: MemoryEventProvider<A, ExplPrec>,
    private val graphPatternCompiler: GraphPatternCompiler<T, *>,
    private val graphPatternSolver: GraphSolver<T>
) : SafetyChecker<S, A, ExplPrec> {

    override fun check(prec: ExplPrec): SafetyResult<S, A> {
        val eventIds = LinkedList<Int>()
        val rels = LinkedList<Pair<String, Tuple>>()
        val lastIds = LinkedHashMap<S, Int>()
        val initId = nextId(eventIds)
        val initStates = LinkedList(initFunc.getInitStates(prec))
        initStates.forEach { lastIds[it] = initId }
        while (initStates.isNotEmpty()) {
            val state = initStates.pop()
            val lastId = checkNotNull(lastIds[state])
            val actions = actionFunc.getEnabledActionsFor(state)

            val nextStates = actions.map { a ->
                val memEvent = memoryEventProvider[a, prec]
                transFunc.getSuccStates(state, a, prec).onEach { s ->
                    memEvent?.also {
                        val id = nextId(eventIds)
                        rels.add(Pair(memEvent.type().label, Tuple1.of(id)))
                        rels.add(Pair("po", Tuple2.of(lastId, id)))
                        lastIds[s] = id
                    }
                }
            }.flatten()
            initStates.addAll(nextStates)
        }
//        PartialSolver(mcm, CandidateExecutionGraph(eventIds, rels))
        return SafetyResult.unsafe(null, null)

    }

    private fun nextId(list: MutableList<Int>): Int {
        val ret = list.size
        list.add(list.size)
        return ret
    }
}