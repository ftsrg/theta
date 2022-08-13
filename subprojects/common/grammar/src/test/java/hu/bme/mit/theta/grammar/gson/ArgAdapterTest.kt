/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.grammar.gson

import com.google.gson.Gson
import com.google.gson.reflect.TypeToken
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.ArgNode
import hu.bme.mit.theta.grammar.gson.stubs.ActionStub
import hu.bme.mit.theta.grammar.gson.stubs.PartialOrdStub
import hu.bme.mit.theta.grammar.gson.stubs.StateStub
import org.junit.Assert
import org.junit.Test
import java.util.stream.Collectors


class ArgAdapterTest {
    private val arg = ARG.create<StateStub, ActionStub>(PartialOrdStub)
    private val act = ActionStub("A")

    private val s0 = arg.createInitNode(StateStub("s0"), false)
    private val s10 = arg.createSuccNode(s0, act, StateStub("s10"), false)
    private val s20 = arg.createSuccNode(s10, act, StateStub("s20"), true)
    private val s21 = arg.createSuccNode(s10, act, StateStub("s21"), false)
    private val s11 = arg.createSuccNode(s0, act, StateStub("s11"), true)
    private val s12 = arg.createSuccNode(s0, act, StateStub("s12"), false)
    private val nodes = arg.nodes.collect(Collectors.toList())

    init {
        s12.cover(s11)
    }

    @Test
    fun testRoundTrip() {
        val gson = Gson()
        val argAdapter = ArgAdapter(arg)
        val json = gson.toJson(ArgAdapter(arg))
        val type = object: TypeToken<ArgAdapter<StateStub, ActionStub>>() {}.type
        val parsedBack = gson.fromJson<ArgAdapter<StateStub,ActionStub>>(json, type)
        Assert.assertEquals(argAdapter, parsedBack)
        val arg = parsedBack.instantiate(PartialOrdStub)
        Assert.assertEquals(this.arg, arg)
    }


}