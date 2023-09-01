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
import com.google.gson.GsonBuilder
import com.google.gson.TypeAdapter
import com.google.gson.reflect.TypeToken
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.grammar.dsl.ExprTest
import hu.bme.mit.theta.grammar.dsl.SimpleScope
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import hu.bme.mit.theta.grammar.dsl.type.TypeWrapper
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.lang.reflect.Type
import java.util.*

class TestGson {

    companion object {

        private fun explArgAdapterHelper(): Type =
            TypeToken.getParameterized(
                TypeToken.get(ArgAdapterHelper::class.java).type,
                TypeToken.get(ExplState::class.java).type,
                TypeToken.get(SimpleStmtAction::class.java).type,
            ).type

        private fun explArgHelper(): Type =
            TypeToken.getParameterized(
                TypeToken.get(ARG::class.java).type,
                TypeToken.get(ExplState::class.java).type,
                TypeToken.get(SimpleStmtAction::class.java).type,
            ).type

        private fun explTraceHelper() =
            TypeToken.getParameterized(
                TypeToken.get(Trace::class.java).type,
                TypeToken.get(ExplState::class.java).type,
                TypeToken.get(SimpleStmtAction::class.java).type,
            ).type

        private fun predArgAdapterHelper(): Type =
            TypeToken.getParameterized(
                TypeToken.get(ArgAdapterHelper::class.java).type,
                TypeToken.get(PredState::class.java).type,
                TypeToken.get(SimpleStmtAction::class.java).type,
            ).type

        private fun predArgHelper(): Type =
            TypeToken.getParameterized(
                TypeToken.get(ARG::class.java).type,
                TypeToken.get(PredState::class.java).type,
                TypeToken.get(SimpleStmtAction::class.java).type,
            ).type

        private fun predTraceHelper() =
            TypeToken.getParameterized(
                TypeToken.get(Trace::class.java).type,
                TypeToken.get(PredState::class.java).type,
                TypeToken.get(SimpleStmtAction::class.java).type,
            ).type

        private fun getExplBuilder(gsonSuppl: () -> Gson): GsonBuilder {
            val gsonBuilder = GsonBuilder()

            gsonBuilder.registerTypeHierarchyAdapter(ARG::class.java,
                ArgAdapter(gsonSuppl, { ExplOrd.getInstance() }, { explArgAdapterHelper() }))
            gsonBuilder.registerTypeHierarchyAdapter(Trace::class.java,
                TraceAdapter(gsonSuppl, { ExplState::class.java }, SimpleStmtAction::class.java))
            gsonBuilder.registerTypeHierarchyAdapter(SafetyResult::class.java,
                SafetyResultAdapter(gsonSuppl, { explArgHelper() }, { explTraceHelper() }))

            return gsonBuilder
        }

        private fun getPredBuilder(gsonSuppl: () -> Gson): GsonBuilder {
            val gsonBuilder = GsonBuilder()

            gsonBuilder.registerTypeHierarchyAdapter(ARG::class.java,
                ArgAdapter(gsonSuppl, { PartialOrd<PredState> { a, b -> true } }, { predArgAdapterHelper() }))
            gsonBuilder.registerTypeHierarchyAdapter(Trace::class.java,
                TraceAdapter(gsonSuppl, { PredState::class.java }, SimpleStmtAction::class.java))
            gsonBuilder.registerTypeHierarchyAdapter(SafetyResult::class.java,
                SafetyResultAdapter(gsonSuppl, { predArgHelper() }, { predTraceHelper() }))

            return gsonBuilder
        }

        val x = Var("x", Int())
        private fun getGson(gsonBuilder: GsonBuilder, gsonSuppl: () -> Gson): Gson {
            val symbolTable = SymbolTable()
            val symbol = ExprTest.NamedSymbol(x.name)
            symbolTable.add(symbol)
            val scope = SimpleScope(symbolTable)
            val env = Env()
            env.define(symbol, x)

            gsonBuilder.registerTypeHierarchyAdapter(VarDecl::class.java,
                VarDeclAdapter(gsonSuppl, scope, env, false))
            gsonBuilder.registerTypeHierarchyAdapter(Stmt::class.java,
                StringTypeAdapter { StatementWrapper(it, scope).instantiate(env) })
            gsonBuilder.registerTypeHierarchyAdapter(Expr::class.java,
                StringTypeAdapter { ExpressionWrapper(scope, it).instantiate(env) })
            gsonBuilder.registerTypeHierarchyAdapter(hu.bme.mit.theta.core.type.Type::class.java,
                StringTypeAdapter { TypeWrapper(it).instantiate() })
            gsonBuilder.registerTypeHierarchyAdapter(VarIndexing::class.java,
                StringTypeAdapter { BasicVarIndexing.fromString(it, scope, env) })
            gsonBuilder.registerTypeHierarchyAdapter(ExplState::class.java, ExplStateAdapter(scope, env))
            gsonBuilder.registerTypeHierarchyAdapter(PredState::class.java,
                PredStateAdapter(gsonSuppl, scope, env))
            gsonBuilder.registerTypeHierarchyAdapter(Pair::class.java, PairAdapter<Any, Any>(gsonSuppl))
            gsonBuilder.registerTypeHierarchyAdapter(Triple::class.java, TripleAdapter<Any, Any, Any>(gsonSuppl))
            gsonBuilder.registerTypeHierarchyAdapter(Optional::class.java, OptionalAdapter<Any>(gsonSuppl))

            gsonBuilder.registerTypeAdapter(SimpleStmtAction::class.java, SimpleStmtActionAdapter(gsonSuppl))

            return gsonBuilder.create()
        }
    }

    @Test
    fun testExplArgAdapter() {
        lateinit var gson: Gson;
        gson = getGson(getExplBuilder { gson }) { gson }

        val arg = ARG.create<ExplState, StmtAction>(ExplOrd.getInstance())

        val initNode = arg.createInitNode(ExplState.bottom(), false)
        val otherNode = arg.createSuccNode(initNode, SimpleStmtAction(SkipStmt.getInstance()), ExplState.top(), false)

        val serialized = gson.toJson(arg)
        val parsedBack = gson.fromJson(serialized, ARG::class.java)
        Assertions.assertEquals(arg.initNodes.count(), parsedBack.initNodes.count())
        Assertions.assertEquals(arg.nodes.count(), parsedBack.nodes.count())
    }

    @Test
    fun testPredArgAdapter() {
        lateinit var gson: Gson;
        gson = getGson(getPredBuilder { gson }) { gson }

        val arg = ARG.create<PredState, StmtAction> { _, _ -> false }

        val initNode = arg.createInitNode(PredState.bottom(), false)
        val otherNode = arg.createSuccNode(initNode, SimpleStmtAction(Havoc(x)), PredState.of(), false)

        val serialized = gson.toJson(arg)
        val parsedBack = gson.fromJson(serialized, ARG::class.java)
        Assertions.assertEquals(arg.initNodes.count(), parsedBack.initNodes.count())
        Assertions.assertEquals(arg.nodes.count(), parsedBack.nodes.count())
    }

    @Test
    fun testExplTrace() {
        lateinit var gson: Gson;
        gson = getGson(getExplBuilder { gson }) { gson }

        val trace = Trace.of(
            listOf(ExplState.of(ImmutableValuation.builder().put(x, Int(1)).build()),
                ExplState.of(ImmutableValuation.builder().put(x, Int(2)).build())),
            listOf(SimpleStmtAction(SkipStmt.getInstance()))
        )

        val serialized = gson.toJson(trace)
        val parsedBack = gson.fromJson(serialized, Trace::class.java)
        Assertions.assertEquals(trace.length(), parsedBack.length())
    }

    @Test
    fun testOther() {
        lateinit var gson: Gson;
        gson = getGson(getPredBuilder { gson }) { gson }

        val pair = Pair("a", "b")
        val triple = Triple("a", "b", "c")
        val opt = Optional.of(pair)

        Assertions.assertEquals(pair, gson.fromJson(gson.toJson(pair), Pair::class.java))
        Assertions.assertEquals(triple, gson.fromJson(gson.toJson(triple), Triple::class.java))
        Assertions.assertEquals(opt, gson.fromJson(gson.toJson(opt), Optional::class.java))
        Assertions.assertEquals(x, gson.fromJson(gson.toJson(x), VarDecl::class.java))

    }


    class SimpleStmtAction(val stmt: Stmt) : StmtAction() {

        override fun getStmts(): List<Stmt> {
            return listOf(stmt);
        }
    }

    class SimpleStmtActionAdapter(val gsonUtils: () -> Gson) : TypeAdapter<SimpleStmtAction>() {

        override fun write(out: JsonWriter, value: SimpleStmtAction) {
            gsonUtils().toJson(gsonUtils().toJsonTree(value.stmt, Stmt::class.java), out)
        }

        override fun read(`in`: JsonReader): SimpleStmtAction {
            val stmt = gsonUtils().fromJson<Stmt>(`in`, Stmt::class.java)
            return SimpleStmtAction(stmt)
        }

    }

}