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
import com.google.gson.reflect.TypeToken
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.MutableScope
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type

class VarDeclAdapter(val gsonSupplier: () -> Gson, val scope: MutableScope, val env: Env,
    val throwIfNotInScope: Boolean = false) : TypeAdapter<VarDecl<*>>() {

    private lateinit var gson: Gson

    override fun write(writer: JsonWriter, value: VarDecl<*>) {
        initGson()
        writer.beginObject()
        writer.name("name").value(value.name)
        writer.name("type")
        gson.toJson(gson.toJsonTree(value.type), writer)
        writer.endObject()
    }

    override fun read(reader: JsonReader): VarDecl<*> {
        initGson()
        reader.beginObject()
        lateinit var name: String
        lateinit var type: Type
        while (reader.peek() != JsonToken.END_OBJECT) {
            val key = reader.nextName()
            if (key == "name") {
                name = reader.nextString()
            } else if (key == "type") {
                val jsonType = object : TypeToken<Type>() {}.type
                type = gson.fromJson(reader, jsonType)
            }
        }
        reader.endObject()
        val symbol = scope.resolve(name)
        if (symbol.isPresent) {
            val ret: VarDecl<*> = env.eval(symbol.get()) as VarDecl<*>
            check(ret.type == type)
            return ret
        }
        check(!throwIfNotInScope) { "Variable $name is not known." }
        val newSymbol = Symbol { name }
        val varDecl = Var(name, type)
        scope.add(newSymbol)
        env.define(newSymbol, varDecl)
        return varDecl
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }
}