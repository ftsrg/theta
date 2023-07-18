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
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import java.util.*
import kotlin.reflect.KClass

class XcfaActionAdapter(val gsonSupplier: () -> Gson) : TypeAdapter<XcfaAction>() {

    private lateinit var gson: Gson
    override fun write(writer: JsonWriter, value: XcfaAction) {
        initGson()
        writer.beginObject()
        writer.name("pid").value(value.pid)
        writer.name("edge")
        gson.toJson(gson.toJsonTree(value.edge), writer)
        writer.endObject()
    }

    override fun read(reader: JsonReader): XcfaAction {
        initGson()
        var pid: Int? = null
        lateinit var edge: XcfaEdge
        reader.beginObject()
        while (reader.peek() != JsonToken.END_OBJECT) {
            when (reader.nextName()) {
                "pid" -> pid = reader.nextInt()
                "edge" -> edge = gson.fromJson(reader, XcfaEdge::class.java)
            }
        }
        reader.endObject()
        return XcfaAction(pid!!, edge)
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}