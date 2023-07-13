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

import com.google.gson.GsonBuilder
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.xcfa.model.MetaData

class MetaDataAdapter : TypeAdapter<MetaData>() {

    private val gson = GsonBuilder().create()

    override fun write(writer: JsonWriter, value: MetaData) {
        writer.beginObject()
        writer.name("type").value(value.javaClass.name)
        writer.name("content")
        gson.toJson(gson.toJsonTree(value), writer)
        writer.endObject()
    }

    override fun read(reader: JsonReader): MetaData {
        reader.beginObject()
        check(reader.nextName() == "type")
        val typeName = reader.nextString()
        check(reader.nextName() == "content")
        val content: MetaData = gson.fromJson(reader, Class.forName(typeName))
        reader.endObject()
        return content
    }

}