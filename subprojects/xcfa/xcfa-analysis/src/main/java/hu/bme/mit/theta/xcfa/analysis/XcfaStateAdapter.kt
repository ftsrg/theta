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

package hu.bme.mit.theta.xcfa.analysis

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.reflect.TypeToken
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.expr.ExprState

class XcfaStateAdapter<S: ExprState>(val gsonSupplier: () -> Gson) : TypeAdapter<XcfaState<S>>() {
    private lateinit var gson: Gson
    override fun write(writer: JsonWriter, value: XcfaState<S>) {
        initGson()
        writer.beginObject()
        writer.name("processes")
        gson.toJson(gson.toJsonTree(value.processes), writer)
        writer.name("sGlobal")
        writer.beginObject()
        writer.name("type").value(value.sGlobal::class.java.name)
        writer.name("value")
        gson.toJson(gson.toJsonTree(value.sGlobal), writer)
        writer.endObject()
        writer.endObject()
    }

    override fun read(reader: JsonReader): XcfaState<S> {
        initGson()
        lateinit var processes: Map<Int, XcfaProcessState>
        lateinit var sGlobal: S
        reader.beginObject()
        while(reader.peek() != JsonToken.END_OBJECT) {
            when(reader.nextName()) {
                "processes" -> processes = gson.fromJson(reader, object: TypeToken<Map<Int,XcfaProcessState>>(){}.type)
                "sGlobal" -> sGlobal = run {
                    reader.beginObject()
                    lateinit var clazz: Class<*>
                    lateinit var value: Any
                    while(reader.peek() != JsonToken.END_OBJECT) {
                        when(reader.nextName()) {
                            "type" -> clazz = Class.forName(reader.nextString())
                            "value" -> value = gson.fromJson(reader, clazz)
                        }
                    }
                    reader.endObject()
                    value as S
                }
            }
        }
        reader.endObject()
        return XcfaState(processes, sGlobal)
    }

    private fun initGson() {
        if(!this::gson.isInitialized) gson = gsonSupplier()
    }
}