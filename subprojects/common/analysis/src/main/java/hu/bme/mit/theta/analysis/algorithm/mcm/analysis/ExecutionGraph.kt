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

import hu.bme.mit.theta.analysis.algorithm.mcm.mcm.EncodedRelationWrapper
import hu.bme.mit.theta.analysis.algorithm.mcm.mcm.MCM
import hu.bme.mit.theta.common.TupleN
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverStatus

class ExecutionGraph {

    private val events = ArrayList<Int>()
    private val relations = LinkedHashMap<Pair<String, TupleN<Int>>, TVL>()

    fun addEvent(event: Int) {
        events.add(event)
    }

    fun getEvents(): List<Int> = events

    operator fun set(name: String, tuple: TupleN<Int>, value: TVL) {
        relations[Pair(name, tuple)] = value
    }

    operator fun get(name: String, tuple: TupleN<Int>): TVL? {
        return relations[Pair(name, tuple)]
    }

    fun toExpr(mcm: MCM): Expr<BoolType> {
        val expressionCollector = object : Solver {
            private val expressions = ArrayList<Expr<BoolType>>()
            override fun close() = Unit
            override fun check(): SolverStatus = error("Unsupported")
            override fun push() = Unit
            override fun pop(n: Int) = Unit
            override fun reset() = expressions.clear()
            override fun getStatus(): SolverStatus = error("Unsupported")
            override fun getModel(): Valuation = error("Unsupported")
            override fun getAssertions(): MutableCollection<Expr<BoolType>> = expressions
            override fun add(assertion: Expr<BoolType>) {
                expressions.add(assertion)
            }
        }
        val encodedRelationWrapper = EncodedRelationWrapper(expressionCollector)
        val valuation = MutableValuation()

        mcm.constraints.forEach {
            it.encodeEvents(events, encodedRelationWrapper)
        }

        for (relation in mcm.relations) {
            val eventSet = encodedRelationWrapper[relation.key]
            val recordValue = { tuple: TupleN<Int> ->
                val valueToEncode = relations.getOrDefault(Pair(relation.key, tuple), TVL.UNKNOWN)
                if (valueToEncode != TVL.UNKNOWN)
                    valuation.put(eventSet[tuple], BoolExprs.Bool(valueToEncode == TVL.TRUE))
            }
            for (event1 in events) {
                if (relation.value.arity == 1) {
                    val tuple = TupleN.of(event1)
                    recordValue(tuple)
                } else {
                    for (event2 in events) {
                        val tuple = TupleN.of(event1, event2)
                        recordValue(tuple)
                    }
                }
            }
        }

        expressionCollector.add(valuation.toExpr())
        return And(expressionCollector.assertions)
    }
}

enum class TVL {
    FALSE,
    UNKNOWN,
    TRUE
}