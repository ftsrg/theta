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
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.frontend.FrontendMetadata

class FrontendMetadataAdapter(val gsonSupplier: () -> Gson) : TypeAdapter<FrontendMetadata>() {

  private lateinit var gson: Gson

  override fun write(writer: JsonWriter, value: FrontendMetadata) {
    initGson()
    writer.beginArray()

    for ((owner, tup) in value.lookupKeyValue.entries) {
      writer.beginObject()
      writer.name("owner").value(owner)
      writer.name("values").beginArray()
      for ((key, _val) in tup.entries) {
        writer.beginObject()
        if (_val is String) {
          writer.name(key).value(_val)
        }
        if (_val is Boolean) {
          writer.name(key).value(_val)
        }
        writer.endObject()
      }
      writer.endArray()
      writer.endObject()
    }

    writer.endArray()
  }

  override fun read(reader: JsonReader): FrontendMetadata {
    initGson()

    val lookupKeyValue = mutableMapOf<Int, Map<String, Any>>()

    reader.beginArray()
    while (reader.hasNext()) {
      reader.beginObject()

      var owner: Int? = null
      var values: Map<String, Any>? = null

      while (reader.hasNext()) {
        when (reader.nextName()) {
          "owner" -> {
            owner = reader.nextInt()
          }

          "values" -> {
            values = readValuesArray(reader)
          }

          else -> {
            reader.skipValue()
          }
        }
      }

      reader.endObject()

      if (owner != null && values != null) {
        lookupKeyValue[owner] = values
      }
    }
    reader.endArray()

    return FrontendMetadata(lookupKeyValue)
  }

  private fun readValuesArray(reader: JsonReader): Map<String, Any> {
    val values = mutableMapOf<String, Any>()

    reader.beginArray()
    while (reader.peek() != JsonToken.END_ARRAY) {
      reader.beginObject()
      if (reader.hasNext()) {
        val key = reader.nextName()
        val value = readValue(reader)
        if (value != null) {
          values[key] = value
        }
      }

      reader.endObject()
    }
    reader.endArray()

    return values
  }

  private fun readValue(reader: JsonReader): Any? {
    return when {
      reader.peek() == JsonToken.STRING -> reader.nextString()
      reader.peek() == JsonToken.BOOLEAN -> reader.nextBoolean()
      else -> {
        reader.skipValue()
        null
      }
    }
  }

  private fun initGson() {
    if (!this::gson.isInitialized) gson = gsonSupplier()
  }
}
