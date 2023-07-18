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
import kotlin.reflect.KClass

class PairAdapter<A : Any, B : Any>(val gsonSupplier: () -> Gson) : TypeAdapter<Pair<A, B>>() {

    private lateinit var gson: Gson
    override fun write(writer: JsonWriter, value: Pair<A, B>) {
        initGson()
        writer.beginObject()

        writer.name("first")
        writer.beginObject()
        writer.name("type").value(value.first::class.java.name)
        writer.name("value")
        gson.toJson(gson.toJsonTree(value.first), writer)
        writer.endObject()

        writer.name("second")
        writer.beginObject()
        writer.name("type").value(value.second::class.java.name)
        writer.name("value")
        gson.toJson(gson.toJsonTree(value.second), writer)
        writer.endObject()

        writer.endObject()
    }

    override fun read(reader: JsonReader): Pair<A, B> {
        initGson()
        reader.beginObject()
        lateinit var a: A
        lateinit var b: B

        while (reader.peek() != JsonToken.END_OBJECT) {
            val nextName = reader.nextName()
            reader.beginObject()
            lateinit var clazz: KClass<*>
            lateinit var value: Any
            while (reader.peek() != JsonToken.END_OBJECT) {
                when (reader.nextName()) {
                    "type" -> clazz = Class.forName(reader.nextString()).kotlin
                    "value" -> value = gson.fromJson(reader, clazz.java)
                }
            }
            reader.endObject()
            when (nextName) {
                "first" -> a = value as A
                "second" -> b = value as B
            }
        }

        reader.endObject()
        return Pair(a, b)
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}