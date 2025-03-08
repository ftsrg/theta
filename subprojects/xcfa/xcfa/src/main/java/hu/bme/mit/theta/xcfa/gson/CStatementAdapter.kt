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

import com.google.gson.GsonBuilder
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement

class CStatementAdapter : TypeAdapter<CStatement>() {

  private val gson = GsonBuilder().create()

  override fun write(writer: JsonWriter, value: CStatement) {
    writer.beginObject()

    writer.endObject()
  }

  override fun read(reader: JsonReader): CStatement? {
    reader.beginObject()

    reader.endObject()
    return null
  }
}
