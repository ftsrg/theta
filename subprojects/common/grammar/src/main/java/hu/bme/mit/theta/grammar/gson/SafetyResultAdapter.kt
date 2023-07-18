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
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.Statistics
import java.lang.reflect.Type
import java.util.*

class SafetyResultAdapter(
    val gsonSupplier: () -> Gson,
    private val argTypeSupplier: () -> Type,
    private val traceTypeSupplier: () -> Type,
) : TypeAdapter<SafetyResult<out State, out Action>>() {

    private lateinit var gson: Gson
    private lateinit var argType: Type
    private lateinit var traceType: Type

    override fun write(writer: JsonWriter, value: SafetyResult<out State, out Action>) {
        initGson()
        writer.beginObject()
        writer.name("arg")
        gson.toJson(gson.toJsonTree(value.arg), writer)
        writer.name("stats")
//        gson.toJson(gson.toJsonTree(value.stats), writer)
        gson.toJson(gson.toJsonTree(Optional.empty<Statistics>()), writer)
        if (value.isSafe) {
            writer.name("safe").value(true)
        } else {
            val unsafe = value.asUnsafe()
            writer.name("safe").value(false)
            writer.name("trace")
            gson.toJson(gson.toJsonTree(unsafe.trace), writer)
        }
        writer.endObject()
    }

    override fun read(reader: JsonReader): SafetyResult<State, Action> {
        initGson()
        initTypes()
        lateinit var arg: ARG<State, Action>
        lateinit var stats: Optional<Statistics>
        var safe: Boolean? = null
        lateinit var trace: Trace<State, Action>
        reader.beginObject()
        while (reader.peek() != JsonToken.END_OBJECT) {
            when (reader.nextName()) {
                "arg" -> arg = gson.fromJson(reader, argType)
                "stats" -> stats = gson.fromJson(reader, Optional::class.java)
                "safe" -> safe = reader.nextBoolean()
                "trace" -> trace = gson.fromJson(reader, traceType)
            }
        }
        reader.endObject()
        return if (stats.isEmpty)
            if (safe == true) SafetyResult.safe(arg) else SafetyResult.unsafe(trace, arg)
        else
            if (safe == false) SafetyResult.safe(arg, stats.get()) else SafetyResult.unsafe(trace,
                arg, stats.get())
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }

    private fun initTypes() {
        if (!this::traceType.isInitialized) traceType = traceTypeSupplier()
        if (!this::argType.isInitialized) argType = argTypeSupplier()
    }
}