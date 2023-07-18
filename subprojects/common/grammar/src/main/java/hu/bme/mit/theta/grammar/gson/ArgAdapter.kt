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

package hu.bme.mit.theta.grammar.gson

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import java.lang.reflect.Type

class ArgAdapter(val gsonSupplier: () -> Gson,
    private val partialOrdSupplier: () -> PartialOrd<out State>,
    private val argTypeSupplier: () -> Type) : TypeAdapter<ARG<*, *>>() {

    private lateinit var gson: Gson
    private lateinit var partialOrd: PartialOrd<State>
    private lateinit var argType: Type

    override fun write(writer: JsonWriter, value: ARG<*, *>) {
        initGson()
        gson.toJson(gson.toJsonTree(ArgAdapterHelper(value)), writer)
    }

    override fun read(reader: JsonReader): ARG<*, *> {
        initGson()
        if (!this::partialOrd.isInitialized) partialOrd = partialOrdSupplier() as PartialOrd<State>
        if (!this::argType.isInitialized) argType = argTypeSupplier()
        val argAdapterHelper: ArgAdapterHelper<State, Action> = gson.fromJson(reader, argType)
        return argAdapterHelper.instantiate(partialOrd)
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}