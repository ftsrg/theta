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
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper

//class StateAdapter(val gsonSupplier: () -> Gson, val scope: Scope, val env: Env): TypeAdapter<State>() {
//    lateinit var gson: Gson
//    override fun write(writer: JsonWriter, value: State) {
//        initGson()
//        writer.beginObject()
//        writer.name("type").value(value::class.qualifiedName)
//        writer.name("value")
//        when(value) {
//            is ExplState -> ExplStateAdapter(scope, env).write(writer, value)
//            else -> TODO("Unknown state type: " + value::class.qualifiedName)
//        }
//        writer.endObject()
//    }
//
//    override fun read(reader: JsonReader): State {
//        initGson()
//        reader.beginObject()
//        lateinit var s: State
//        if (reader.peek() != JsonToken.END_OBJECT) {
//            lateinit var clazz: KClass<*>
//            lateinit var value: Any
//            while (reader.peek() != JsonToken.END_OBJECT) {
//                when(reader.nextName()) {
//                    "type" -> clazz = Class.forName(reader.nextString()).kotlin
//                    "value" -> value = when(clazz) {
//                        ExplState::class.java -> ExplStateAdapter(scope, env).read(reader)
//                        else -> TODO("Unknown type " + clazz.qualifiedName)
//                    }
//                }
//            }
//            s = value as State
//        }
//        reader.endObject()
//        return s
//    }
//
//    private fun initGson() {
//        if(!this::gson.isInitialized) gson = gsonSupplier()
//    }
//}

class ExplStateAdapter(val scope: Scope, val env: Env): TypeAdapter<ExplState>() {
    override fun write(writer: JsonWriter, value: ExplState) {
        writer.beginObject()
        writer.name("bottom").value(value.isBottom)
        writer.name("decls").beginArray()
        value.toMap().forEach {
            writer.beginObject().name(it.key.name).value(it.value.toString()).endObject()
        }
        writer.endArray().endObject()
    }

    override fun read(reader: JsonReader): ExplState {
        var ret: ExplState? = null
        reader.beginObject()
        check(reader.nextName() == "bottom")
        if(reader.nextBoolean()) ret = ExplState.bottom()
        check(reader.nextName() == "decls")
        reader.beginArray()
        val mutableValuation = MutableValuation()
        while(reader.peek() != JsonToken.END_ARRAY) {
            reader.beginObject()
            val name = reader.nextName()
            val variable: VarDecl<*> = env.eval(scope.resolve(name.lowercase()).orElseThrow()) as VarDecl<*>
            val value = ExpressionWrapper(scope, reader.nextString()).instantiate(env) as LitExpr<*>
            mutableValuation.put(variable, value)
            reader.endObject()
        }
        if(ret == null) ret = ExplState.of(mutableValuation)
        reader.endArray()
        reader.endObject()
        return ret!!
    }

}