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
package hu.bme.mit.theta.xcfa.cli.params

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.xcfa.passes.LbePass

class SpecFrontendConfigTypeAdapter(val gsonSupplier: () -> Gson) :
  TypeAdapter<FrontendConfig<*>>() {

  private lateinit var gson: Gson

  override fun write(writer: JsonWriter, value: FrontendConfig<*>) {
    initGson()
    writer.beginObject()

    writer.name("lbeLevel").value(value.lbeLevel.name)
    writer.name("loopUnroll").value(value.loopUnroll)
    writer.name("inputType").value(value.inputType.name)
    writer.name("specConfig")
    if (value.specConfig != null) {
      writer.beginObject()
      writer.name("type").value(value.specConfig?.javaClass?.typeName)
      writer.name("value")
      gson.toJson(gson.toJsonTree(value.specConfig), writer)
      writer.endObject()
    } else {
      writer.nullValue()
    }

    writer.endObject()
  }

  override fun read(reader: JsonReader): FrontendConfig<*> {
    initGson()

    // Prepare variables to hold deserialized data
    val instance = FrontendConfig<SpecFrontendConfig>()

    reader.beginObject()
    while (reader.hasNext()) {
      when (reader.nextName()) {
        "lbeLevel" -> instance.lbeLevel = LbePass.LbeLevel.valueOf(reader.nextString())
        "loopUnroll" -> instance.loopUnroll = reader.nextInt()
        "inputType" -> instance.inputType = InputType.valueOf(reader.nextString())
        "specConfig" -> instance.specConfig = readSpecConfig(reader)
        else -> reader.skipValue()
      }
    }
    reader.endObject()

    return instance
  }

  private fun readSpecConfig(reader: JsonReader): SpecFrontendConfig? =
    if (reader.peek() == JsonToken.NULL) {
      null
    } else {
      lateinit var specConfig: SpecFrontendConfig
      reader.beginObject()
      lateinit var clazz: Class<*>
      while (reader.hasNext()) {
        when (reader.nextName()) {
          "type" -> clazz = Class.forName(reader.nextString())
          "value" -> specConfig = gson.fromJson(reader, clazz)
          else -> reader.skipValue()
        }
      }
      reader.endObject()
      specConfig
    }

  private fun initGson() {
    if (!this::gson.isInitialized) gson = gsonSupplier()
  }
}

class SpecBackendConfigTypeAdapter(val gsonSupplier: () -> Gson) : TypeAdapter<BackendConfig<*>>() {

  private lateinit var gson: Gson

  override fun write(writer: JsonWriter, value: BackendConfig<*>) {
    initGson()
    writer.beginObject()

    writer.name("backend").value(value.backend.name)
    writer.name("solverHome").value(value.solverHome)
    writer.name("timeoutMs").value(value.timeoutMs)
    writer.name("inProcess").value(value.inProcess)
    writer.name("specConfig")
    if (value.specConfig != null) {
      writer.beginObject()
      writer.name("type").value(value.specConfig?.javaClass?.typeName)
      writer.name("value")
      gson.toJson(gson.toJsonTree(value.specConfig), writer)
      writer.endObject()
    } else {
      writer.nullValue()
    }

    writer.endObject()
  }

  override fun read(reader: JsonReader): BackendConfig<*> {
    initGson()

    // Prepare variables to hold deserialized data
    val instance = BackendConfig<SpecBackendConfig>()

    reader.beginObject()
    while (reader.hasNext()) {
      when (reader.nextName()) {
        "backend" -> instance.backend = Backend.valueOf(reader.nextString())
        "solverHome" -> instance.solverHome = reader.nextString()
        "timeoutMs" -> instance.timeoutMs = reader.nextLong()
        "inProcess" -> instance.inProcess = reader.nextBoolean()
        "specConfig" -> instance.specConfig = readSpecConfig(reader)
        else -> reader.skipValue()
      }
    }
    reader.endObject()

    return instance
  }

  private fun readSpecConfig(reader: JsonReader): SpecBackendConfig? =
    if (reader.peek() == JsonToken.NULL) {
      null
    } else {
      lateinit var specConfig: SpecBackendConfig
      reader.beginObject()
      lateinit var clazz: Class<*>
      while (reader.hasNext()) {
        when (reader.nextName()) {
          "type" -> clazz = Class.forName(reader.nextString())
          "value" -> specConfig = gson.fromJson(reader, clazz)
          else -> reader.skipValue()
        }
      }
      reader.endObject()
      specConfig
    }

  private fun initGson() {
    if (!this::gson.isInitialized) gson = gsonSupplier()
  }
}
