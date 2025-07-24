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
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.CStmtCounter
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait

class ParseContextAdapter(val gsonSupplier: () -> Gson) : TypeAdapter<ParseContext>() {

  private lateinit var gson: Gson

  override fun write(writer: JsonWriter, value: ParseContext) {
    initGson()
    writer.beginObject()

    writer.name("arithmeticTraits")
    writer.beginArray()
    for (arithmeticTrait in value.arithmeticTraits) {
      writer.value(arithmeticTrait.name)
    }
    writer.endArray()
    writer.name("architecture").value(value.architecture.name)
    writer.name("arithmetic").value(value.arithmetic.name)
    writer.name("multiThreading").value(value.multiThreading)

    writer.name("cStmtCounter")
    gson.toJson(gson.toJsonTree(value.cStmtCounter), writer)

    writer.name("metadata")
    gson.toJson(gson.toJsonTree(value.metadata), writer)

    writer.endObject()
  }

  override fun read(reader: JsonReader): ParseContext {
    initGson()

    var metadata: FrontendMetadata? = null
    var cStmtCounter: CStmtCounter? = null
    var arithmeticTraits: MutableSet<ArithmeticTrait> = mutableSetOf()
    var architecture: ArchitectureConfig.ArchitectureType? = null
    var multiThreading: Boolean? = null
    var arithmetic: ArchitectureConfig.ArithmeticType? = null

    reader.beginObject()
    while (reader.hasNext()) {
      when (reader.nextName()) {
        "metadata" -> {
          metadata = gson.fromJson(reader, FrontendMetadata::class.java)
        }

        "cStmtCounter" -> {
          cStmtCounter = gson.fromJson(reader, CStmtCounter::class.java)
        }

        "bitwiseOption" -> {
          reader.beginArray()
          while (reader.peek() != JsonToken.END_ARRAY) {
            val optionName = reader.nextString()
            arithmeticTraits.add(ArithmeticTrait.valueOf(optionName))
          }
          reader.endArray()
        }

        "architecture" -> {
          val architectureName = reader.nextString()
          architecture = ArchitectureConfig.ArchitectureType.valueOf(architectureName)
        }

        "multiThreading" -> {
          multiThreading = reader.nextBoolean()
        }

        "arithmetic" -> {
          val arithmeticName = reader.nextString()
          arithmetic = ArchitectureConfig.ArithmeticType.valueOf(arithmeticName)
        }

        else -> {
          reader.skipValue()
        }
      }
    }
    reader.endObject()

    return ParseContext(
      metadata,
      cStmtCounter,
      arithmeticTraits,
      architecture,
      multiThreading,
      arithmetic,
    )
  }

  private fun initGson() {
    if (!this::gson.isInitialized) gson = gsonSupplier()
  }
}
