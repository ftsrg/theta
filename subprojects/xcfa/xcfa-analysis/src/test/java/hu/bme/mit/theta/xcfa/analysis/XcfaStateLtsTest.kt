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

package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.analysis.por.XcfaAasporLts
import hu.bme.mit.theta.xcfa.analysis.por.XcfaSporLts
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.util.*
import java.util.function.Predicate

class XcfaStateLtsTest {

    @Test
    fun testApply() {
        val actionOrder: MutableList<(XcfaState<ExplState>) -> XcfaAction> = ArrayList()
        val expectations: MutableList<Predicate<XcfaState<ExplState>>> = ArrayList()
        val lts = getXcfaLts()
        lateinit var initState: XcfaState<ExplState>
        lateinit var xcfa: XCFA

        val edges: MutableList<XcfaEdge> = ArrayList()
        xcfa = xcfa("example") {
            val proc1 = procedure("proc1") {
                val a = "a" type IntExprs.Int() direction ParamDirection.IN
                val b = "b" type IntExprs.Int() direction ParamDirection.OUT

                edges.add((init to final) {
                    b assign a.ref
                })
            }
            val main = procedure("main") {
                val tmp = "tmp" type IntExprs.Int()
                edges.add((init to "L1") {
                    proc1("1", tmp.ref)
                })
                edges.add(("L1" to "L2") {
                    tmp.start(proc1, tmp.ref)
                })
                edges.add(("L2" to final) {
                    tmp.join()
                })
            }

            main.start()
        }
        initState = XcfaState(
            xcfa,
            mapOf(
                Pair(0,
                    XcfaProcessState(
                        locs = LinkedList(listOf(edges[1].source)),
                        varLookup = LinkedList(listOf(createLookup(xcfa.initProcedures[0].first, "T0", "P0")))
                    )
                )
            ),
            ExplState.bottom()
        )
        val sporLts = XcfaSporLts(xcfa)
        val aasporLts = XcfaAasporLts(xcfa, LinkedHashMap())

        actionOrder.add { XcfaAction(0, edges[1]) }
        expectations.add {
            it.processes[0]!!.locs.size == 2 && it.processes[0]!!.locs.peek() == edges[0].source &&
                lts.getEnabledActionsFor(it).size == 1 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        actionOrder.add { XcfaAction(0, edges[0]) }
        expectations.add {
            it.processes[0]!!.locs.size == 2 && it.processes[0]!!.locs.peek() == edges[0].target &&
                lts.getEnabledActionsFor(it).size == 1 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        actionOrder.add { XcfaAction(0, XcfaEdge(edges[0].target, edges[0].target, ReturnLabel(NopLabel))) }
        expectations.add {
            it.processes[0]!!.locs.size == 1 && it.processes[0]!!.locs.peek() == edges[1].target &&
                lts.getEnabledActionsFor(it).size == 1 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        actionOrder.add { XcfaAction(0, edges[2]) }
        expectations.add {
            it.processes.size == 2 &&
                it.processes[0]!!.locs.size == 1 && it.processes[0]!!.locs.peek() == edges[2].target &&
                it.processes[it.foreignKey()!!]!!.locs.size == 1 && it.processes[it.foreignKey()!!]!!.locs.peek() == edges[0].source &&
                lts.getEnabledActionsFor(it).size == 2 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        actionOrder.add { s -> XcfaAction(s.foreignKey()!!, edges[0]) }
        expectations.add {
            it.processes.size == 2 &&
                it.processes[0]!!.locs.size == 1 && it.processes[0]!!.locs.peek() == edges[2].target &&
                it.processes[it.foreignKey()!!]!!.locs.size == 1 && it.processes[it.foreignKey()!!]!!.locs.peek() == edges[0].target &&
                lts.getEnabledActionsFor(it).size == 2 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        actionOrder.add { s ->
            XcfaAction(s.foreignKey()!!, XcfaEdge(edges[0].target, edges[0].target, ReturnLabel(NopLabel)))
        }
        expectations.add {
            it.processes.size == 1 && it.processes[0]!!.locs.size == 1 && it.processes[0]!!.locs.peek() == edges[2].target &&
                lts.getEnabledActionsFor(it).size == 1 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        actionOrder.add { XcfaAction(0, edges[3]) }
        expectations.add {
            it.processes[0]!!.locs.size == 1 && it.processes[0]!!.locs.peek() == edges[3].target &&
                lts.getEnabledActionsFor(it).size == 1 &&
                sporLts.getEnabledActionsFor(it).size == 1 &&
                aasporLts.getEnabledActionsFor(it, emptyList(), ExplPrec.empty()).size == 1
        }

        var state = initState
        for ((index, xcfaAction) in actionOrder.withIndex()) {
            println("Test $index: $xcfaAction")
            val newState = state.apply(xcfaAction(state))
            assertTrue(expectations[index].test(newState.first))
            state = newState.first
            println("Test $index OK")
        }
    }
}

private fun XcfaState<*>.foreignKey(): Int? =
    processes.keys.firstOrNull { key -> key != 0 }
