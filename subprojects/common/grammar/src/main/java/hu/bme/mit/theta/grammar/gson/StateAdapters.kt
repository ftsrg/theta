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
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper

class ExplStateAdapter(val scope: Scope, val env: Env) : TypeAdapter<ExplState>() {

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
        if (reader.nextBoolean()) ret = ExplState.bottom()
        check(reader.nextName() == "decls")
        reader.beginArray()
        val mutableValuation = MutableValuation()
        while (reader.peek() != JsonToken.END_ARRAY) {
            reader.beginObject()
            val name = reader.nextName()
            val variable: VarDecl<*> = env.eval(scope.resolve(name).orElseThrow()) as VarDecl<*>
            val value = ExpressionWrapper(scope, reader.nextString()).instantiate(env) as LitExpr<*>
            mutableValuation.put(variable, value)
            reader.endObject()
        }
        if (ret == null) ret = ExplState.of(mutableValuation)
        reader.endArray()
        reader.endObject()
        return ret!!
    }

}

class PredStateAdapter(val gsonSupplier: () -> Gson, val scope: Scope, val env: Env) :
    TypeAdapter<PredState>() {

    lateinit var gson: Gson
    override fun write(writer: JsonWriter, value: PredState) {
        initGson()
        writer.beginObject()
        writer.name("bottom").value(value.isBottom)
        writer.name("preds")
        gson.toJson(gson.toJsonTree(value.preds), writer)
        writer.endObject()
    }

    override fun read(reader: JsonReader): PredState {
        initGson()
        var ret: PredState? = null
        reader.beginObject()
        check(reader.nextName() == "bottom")
        if (reader.nextBoolean()) ret = PredState.bottom()
        check(reader.nextName() == "preds")
        val preds = gson.fromJson<Set<Expr<BoolType>>>(reader,
            object : TypeToken<Set<Expr<BoolType>>>() {}.type)
        if (ret == null) ret = PredState.of(preds)
        reader.endObject()
        return ret!!
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }

}