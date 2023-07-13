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
import com.google.gson.reflect.TypeToken
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import java.lang.reflect.Type

class TraceAdapter(val gsonSupplier: () -> Gson, private val stateTypeSupplier: () -> Type,
    private val actionType: Type) : TypeAdapter<Trace<*, *>>() {

    private lateinit var gson: Gson
    private lateinit var stateType: Type

    override fun write(writer: JsonWriter, value: Trace<*, *>) {
        initGson()
        writer.beginObject()
        writer.name("states")
        gson.toJson(gson.toJsonTree(value.states), writer)
        writer.name("actions")
        gson.toJson(gson.toJsonTree(value.actions), writer)
        writer.endObject()
    }

    override fun read(reader: JsonReader): Trace<*, *> {
        initGson()
        if (!this::stateType.isInitialized) stateType = stateTypeSupplier()
        reader.beginObject()
        check(reader.nextName() == "states")
        val stateList: List<State> = gson.fromJson(reader,
            TypeToken.getParameterized(TypeToken.get(List::class.java).type, stateType).type)
        check(reader.nextName() == "actions")
        val actionList: List<Action> = gson.fromJson(reader,
            TypeToken.getParameterized(TypeToken.get(List::class.java).type, actionType).type)
        reader.endObject()
        return Trace.of(stateList, actionList)
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}