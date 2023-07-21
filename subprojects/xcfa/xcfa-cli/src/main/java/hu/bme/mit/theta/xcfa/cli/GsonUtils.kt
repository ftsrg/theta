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

package hu.bme.mit.theta.xcfa.cli

import com.google.gson.Gson
import com.google.gson.GsonBuilder
import com.google.gson.reflect.TypeToken
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.ARG
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import hu.bme.mit.theta.grammar.dsl.type.TypeWrapper
import hu.bme.mit.theta.grammar.gson.*
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.xcfa.XcfaScope
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaActionAdapter
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.XcfaStateAdapter
import hu.bme.mit.theta.xcfa.getSymbols
import hu.bme.mit.theta.xcfa.gson.*
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.util.*

private fun argAdapterHelper(stateType: java.lang.reflect.Type): java.lang.reflect.Type =
    TypeToken.getParameterized(
        TypeToken.get(ArgAdapterHelper::class.java).type,
        TypeToken.getParameterized(TypeToken.get(XcfaState::class.java).type, stateType).type,
        TypeToken.get(XcfaAction::class.java).type,
    ).type

private fun argHelper(stateType: java.lang.reflect.Type): java.lang.reflect.Type =
    TypeToken.getParameterized(
        TypeToken.get(ARG::class.java).type,
        TypeToken.getParameterized(TypeToken.get(XcfaState::class.java).type, stateType).type,
        TypeToken.get(XcfaAction::class.java).type,
    ).type

private fun traceHelper(stateType: java.lang.reflect.Type): java.lang.reflect.Type =
    TypeToken.getParameterized(
        TypeToken.get(Trace::class.java).type,
        TypeToken.getParameterized(TypeToken.get(XcfaState::class.java).type, stateType).type,
        TypeToken.get(XcfaAction::class.java).type,
    ).type

@JvmOverloads
internal fun getGson(xcfa: XCFA, domain: () -> Domain = { error("Domain needs to be specified.") },
    solver: () -> Solver = { error("Solver is necessary.") }): Gson {
    val (scope, env) = xcfa.getSymbols()
    return getGson(scope, env, false, domain, solver)
}

@JvmOverloads
internal fun getGson(domain: () -> Domain = { error("Domain needs to be specified.") },
    solver: () -> Solver = { error("Solver is necessary.") }): Gson {
    return getGson(XcfaScope(SymbolTable()), Env(), true, domain, solver)
}

private fun getGson(scope: XcfaScope, env: Env, newScope: Boolean, domain: () -> Domain,
    solver: () -> Solver): Gson {
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
    gsonBuilder.registerTypeHierarchyAdapter(ExplState::class.java, ExplStateAdapter(scope, env))
    gsonBuilder.registerTypeHierarchyAdapter(PredState::class.java,
        PredStateAdapter({ gson }, scope, env))
    gsonBuilder.registerTypeHierarchyAdapter(XcfaLabel::class.java,
        XcfaLabelAdapter(scope, env, { gson }))
    gsonBuilder.registerTypeHierarchyAdapter(MetaData::class.java, MetaDataAdapter())
    gsonBuilder.registerTypeHierarchyAdapter(Pair::class.java, PairAdapter<Any, Any> { gson })
    gsonBuilder.registerTypeHierarchyAdapter(Optional::class.java, OptionalAdapter<Any> { gson })
    gsonBuilder.registerTypeHierarchyAdapter(XcfaState::class.java,
        XcfaStateAdapter({ gson }) { domain().stateType })
    gsonBuilder.registerTypeHierarchyAdapter(XcfaAction::class.java, XcfaActionAdapter { gson })
    gsonBuilder.registerTypeHierarchyAdapter(Trace::class.java, TraceAdapter({ gson }, {
        TypeToken.getParameterized(TypeToken.get(XcfaState::class.java).type,
            domain().stateType).type
    }, TypeToken.get(XcfaAction::class.java).type))
    gsonBuilder.registerTypeHierarchyAdapter(ARG::class.java,
        ArgAdapter({ gson }, { domain().partialOrd(solver()) },
            { argAdapterHelper(domain().stateType) }))
    gsonBuilder.registerTypeHierarchyAdapter(SafetyResult::class.java,
        SafetyResultAdapter({ gson }, { argHelper(domain().stateType) },
            { traceHelper(domain().stateType) }))
    gsonBuilder.registerTypeHierarchyAdapter(ParseContext::class.java,
        ParseContextAdapter { gson })
    gson = gsonBuilder.create()
    return gson
}