/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
    override fun write(writer: JsonWriter, value: T) {
        writer.beginObject()
        if(value != null) writer.name("content").value(value.toString())
        writer.endObject()
    }

    override fun read(reader: JsonReader): T? {
        reader.beginObject()
        var ret: T? = null
        if(reader.peek() != JsonToken.END_OBJECT) {
            check(reader.peek() == JsonToken.NAME)
            check(reader.nextName() == "content")
            ret = fromString(reader.nextString())
        }
        reader.endObject()
        return ret
    }

}