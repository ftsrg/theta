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

package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.*

fun XCFA.collectVars(): Iterable<VarDecl<*>> = vars.map { it.wrappedVar }.union(procedures.map { it.vars }.flatten())

fun XCFA.collectAssumes(): Iterable<Expr<BoolType>> = procedures.map { it.edges.map { it.label.collectAssumes() }.flatten() }.flatten()
fun XcfaLabel.collectAssumes(): Iterable<Expr<BoolType>> = when(this) {
    is StmtLabel -> when(stmt) {
        is AssumeStmt -> setOf(stmt.cond)
        else -> setOf()
    }
    is NondetLabel -> labels.map { it.collectAssumes() }.flatten()
    is SequenceLabel -> labels.map { it.collectAssumes() }.flatten()
    else -> setOf()
}

fun XCFA.getSymbols(): Pair<Scope, Env> {
    val symbolTable = SymbolTable()
    val scope = XcfaScope(symbolTable)
    val vars = collectVars()
    val env = Env()
    vars.forEach {
        val symbol = Symbol { it.name.lowercase() }
        symbolTable.add(symbol)
        env.define(symbol, it)
    }
    return Pair(scope, env)
}