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
import java.util.*
import kotlin.reflect.KClass

class OptionalAdapter<A : Any>(val gsonSupplier: () -> Gson) : TypeAdapter<Optional<A>>() {

    private lateinit var gson: Gson
    override fun write(writer: JsonWriter, value: Optional<A>) {
        initGson()
        writer.beginObject()
        if (value.isPresent) {
            writer.name("type").value(value.get()::class.qualifiedName)
            writer.name("value")
            gson.toJson(gson.toJsonTree(value.get()), writer)
        }
        writer.endObject()
    }

    override fun read(reader: JsonReader): Optional<A> {
        initGson()
        reader.beginObject()
        var a: A? = null
        if (reader.peek() != JsonToken.END_OBJECT) {
            lateinit var clazz: KClass<*>
            lateinit var value: Any
            while (reader.peek() != JsonToken.END_OBJECT) {
                when (reader.nextName()) {
                    "type" -> clazz = Class.forName(reader.nextString()).kotlin
                    "value" -> value = gson.fromJson(reader, clazz.java)
                }
            }
            a = value as A
        }
        reader.endObject()
        return Optional.ofNullable(a)
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}