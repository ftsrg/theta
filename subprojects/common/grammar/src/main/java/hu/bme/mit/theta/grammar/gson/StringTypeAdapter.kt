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
package hu.bme.mit.theta.grammar.gson

import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter

class StringTypeAdapter<T>(val fromString: (String) -> T) : TypeAdapter<T>() {

  override fun write(writer: JsonWriter, value: T?) {
    if (value != null) writer.value(value.toString()) else writer.nullValue()
  }

  override fun read(reader: JsonReader): T? {
    if (reader.peek() == JsonToken.NULL) {
      return null
    } else {
      check(reader.peek() == JsonToken.STRING)
      return fromString(reader.nextString())
    }
  }
}
