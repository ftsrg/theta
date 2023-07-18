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

package hu.bme.mit.theta.xcfa.gson

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import kotlin.reflect.full.companionObject
import kotlin.reflect.full.functions

class XcfaLabelAdapter(val scope: Scope, val env: Env, val gsonSupplier: () -> Gson) :
    TypeAdapter<XcfaLabel>() {

    private lateinit var gson: Gson

    override fun write(writer: JsonWriter, value: XcfaLabel) {
        initGson()
        writer.beginObject()
        writer.name("type").value(value.javaClass.name)
        writer.name("metadata")
        gson.toJson(gson.toJsonTree(value.metadata), writer)
        if (value is SequenceLabel || value is NondetLabel) {
            writer.name("labels")
            writer.beginArray()
            val labels = if (value is SequenceLabel) value.labels else (value as NondetLabel).labels
            labels.forEach { write(writer, it) }
            writer.endArray()
        } else {
            writer.name("content").value(value.toString())
        }
        writer.endObject()
    }

    override fun read(reader: JsonReader): XcfaLabel {
        initGson()
        reader.beginObject()
        check(reader.nextName() == "type")
        val typeName = reader.nextString()
        val clazz = Class.forName(typeName).kotlin
        check(reader.nextName() == "metadata")
        val metadata: MetaData = gson.fromJson(reader, MetaData::class.java)
        if (clazz == SequenceLabel::class || clazz == NondetLabel::class) {
            check(reader.nextName() == "labels")
            reader.beginArray()
            val labels = ArrayList<XcfaLabel>()
            while (reader.peek() != JsonToken.END_ARRAY) {
                labels.add(read(reader))
            }
            reader.endArray()
            reader.endObject()
            val constr = clazz.constructors.find { it.parameters.size == 2 }
            checkNotNull(constr)
            return constr.call(labels, metadata) as XcfaLabel
        } else {
            check(reader.nextName() == "content")
            val content = reader.nextString()
            val constructor = clazz.companionObject?.functions?.find { it.name == "fromString" }
            checkNotNull(constructor) { "${clazz.simpleName} has no fromString() method." }
            val obj =
                try {
                    constructor.call(clazz.companionObject!!.objectInstance, content, scope, env,
                        metadata)
                } catch (e: Exception) {
                    System.err.println("Could not parse $content\nscope: ${scope}\nenv: $env")
                    throw e
                }
            check(obj is XcfaLabel)
            reader.endObject()
            return obj
        }
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}