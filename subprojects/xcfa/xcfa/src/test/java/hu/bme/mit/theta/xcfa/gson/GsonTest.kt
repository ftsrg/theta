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

import com.google.gson.Gson
import com.google.gson.GsonBuilder
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import hu.bme.mit.theta.grammar.dsl.type.TypeWrapper
import hu.bme.mit.theta.grammar.gson.OptionalAdapter
import hu.bme.mit.theta.grammar.gson.PairAdapter
import hu.bme.mit.theta.grammar.gson.StringTypeAdapter
import hu.bme.mit.theta.grammar.gson.VarDeclAdapter
import hu.bme.mit.theta.xcfa.XcfaScope
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.util.*

class GsonTest {

    private fun getGson(scope: XcfaScope, env: Env, newScope: Boolean): Gson {
        val gsonBuilder = GsonBuilder()
        lateinit var gson: Gson
        gsonBuilder.registerTypeHierarchyAdapter(XcfaLocation::class.java,
            StringTypeAdapter(xcfaLocationAdapter))
        gsonBuilder.registerTypeHierarchyAdapter(XCFA::class.java, XcfaAdapter { gson })
        gsonBuilder.registerTypeHierarchyAdapter(VarDecl::class.java,
            VarDeclAdapter({ gson }, scope, env, !newScope))
        gsonBuilder.registerTypeHierarchyAdapter(Stmt::class.java,
            StringTypeAdapter { StatementWrapper(it, scope).instantiate(env) })
        gsonBuilder.registerTypeHierarchyAdapter(Expr::class.java,
            StringTypeAdapter { ExpressionWrapper(scope, it).instantiate(env) })
        gsonBuilder.registerTypeHierarchyAdapter(Type::class.java,
            StringTypeAdapter { TypeWrapper(it).instantiate() })
        gsonBuilder.registerTypeHierarchyAdapter(VarIndexing::class.java,
            StringTypeAdapter { BasicVarIndexing.fromString(it, scope, env) })
        gsonBuilder.registerTypeHierarchyAdapter(XcfaLabel::class.java,
            XcfaLabelAdapter(scope, env, { gson }))
        gsonBuilder.registerTypeHierarchyAdapter(MetaData::class.java, MetaDataAdapter())
        gsonBuilder.registerTypeHierarchyAdapter(Pair::class.java, PairAdapter<Any, Any> { gson })
        gsonBuilder.registerTypeHierarchyAdapter(Optional::class.java, OptionalAdapter<Any> { gson })
        gson = gsonBuilder.create()
        return gson
    }

    @Test
    fun testRoundtrip() {
        val xcfaSource = xcfa("example") {
            global { "x" type Int() init "0" }
            procedure("main") {
                (init to final) {
                    "proc1"("x")
                }
            }
            procedure("proc1") {
                (init to final) {
                    assume("true")
                }
            }
        }

        val symbolTable = XcfaScope(SymbolTable())
        val x_symbol = NamedSymbol("x")
        symbolTable.add(x_symbol)
        val env = Env()
        env.define(x_symbol, xcfaSource.vars.find { it.wrappedVar.name == "x" }!!.wrappedVar)
        val gson = getGson(symbolTable, env, true)

        val output = gson.fromJson(gson.toJson(xcfaSource), XCFA::class.java)
        println(xcfaSource)
        println(output)
        assertEquals(xcfaSource, output)
    }

}