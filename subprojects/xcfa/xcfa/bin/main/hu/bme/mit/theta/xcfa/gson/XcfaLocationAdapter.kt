/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XcfaLocation

class XcfaLocationAdapter(val gsonSupplier: () -> Gson) : TypeAdapter<XcfaLocation>() {

  private lateinit var gson: Gson

  override fun write(writer: JsonWriter, value: XcfaLocation) {
    initGson()
    writer.beginObject()
    writer.name("name").value(value.name)
    writer.name("initial").value(value.initial)
    writer.name("final").value(value.final)
    writer.name("error").value(value.error)
    writer.name("metadata")
    gson.toJson(gson.toJsonTree(value.metadata), writer)
    writer.endObject()
  }

  override fun read(reader: JsonReader): XcfaLocation {
    initGson()
    reader.beginObject()

    lateinit var name: String
    var initial = false
    var final = false
    var error = false
    var metaData: MetaData? = null

    while (reader.hasNext()) {
      val jsonName = reader.nextName()
      when (jsonName) {
        "name" -> name = reader.nextString()
        "initial" -> initial = reader.nextBoolean()
        "final" -> final = reader.nextBoolean()
        "error" -> error = reader.nextBoolean()
        "metaData" -> metaData = gson.fromJson(reader, MetaData::class.java)
        else -> reader.skipValue()
      }
    }
    reader.endObject()

    return XcfaLocation(name, initial, final, error, metaData ?: EmptyMetaData)
  }

  private fun initGson() {
    if (!this::gson.isInitialized) gson = gsonSupplier()
  }
}
