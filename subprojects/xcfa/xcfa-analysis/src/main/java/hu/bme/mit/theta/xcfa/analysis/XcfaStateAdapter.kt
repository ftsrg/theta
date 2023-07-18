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

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.decl.VarDecl
import java.lang.reflect.Type

class XcfaStateAdapter(val gsonSupplier: () -> Gson, val stateTypeSupplier: () -> Type) :
    TypeAdapter<XcfaState<*>>() {

    private lateinit var gson: Gson
    private lateinit var stateType: Type
    override fun write(writer: JsonWriter, value: XcfaState<*>) {
        initGson()
        writer.beginObject()
        writer.name("processes")
        gson.toJson(gson.toJsonTree(value.processes), writer)
        writer.name("sGlobal")
        gson.toJson(gson.toJsonTree(value.sGlobal), writer)
        writer.name("mutexes")
        gson.toJson(gson.toJsonTree(value.mutexes), writer)
        writer.name("threadLookup")
        gson.toJson(gson.toJsonTree(value.threadLookup), writer)
        writer.name("bottom")
        gson.toJson(gson.toJsonTree(value.bottom), writer)
        writer.endObject()
    }

    override fun read(reader: JsonReader): XcfaState<*> {
        initGson()
        if (!this::stateType.isInitialized) stateType = stateTypeSupplier()
        reader.beginObject()
        check(reader.nextName() == "processes")
        val processes: Map<Int, XcfaProcessState> = gson.fromJson(reader, Map::class.java)
        check(reader.nextName() == "sGlobal")
        val sGlobal: ExprState = gson.fromJson(reader, stateType)
        check(reader.nextName() == "mutexes")
        val mutexes: Map<String, Int> = gson.fromJson(reader, Map::class.java)
        check(reader.nextName() == "threadLookup")
        val threadLookup: Map<VarDecl<*>, Int> = gson.fromJson(reader, Map::class.java)
        check(reader.nextName() == "bottom")
        val bottom: Boolean = gson.fromJson(reader, Boolean::class.java)

        reader.endObject()
        return XcfaState(xcfa = null,
            processes = processes,
            sGlobal = sGlobal,
            mutexes = mutexes,
            threadLookup = threadLookup,
            bottom = bottom)
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}