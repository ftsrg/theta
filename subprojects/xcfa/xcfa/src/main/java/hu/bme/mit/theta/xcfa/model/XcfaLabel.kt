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

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.grammar.dsl.stmt.StatementWrapper
import java.util.Optional
import java.util.StringJoiner

sealed class XcfaLabel {
    open fun toStmt(): Stmt = error("Cannot convert label to statement.")
}

data class InvokeLabel(
        val name: String,
        val params: List<Expr<*>>
) : XcfaLabel() {
    override fun toString(): String {
        val sj = StringJoiner(", ", "(", ")")
        params.forEach { sj.add(it.toString()) }
        return "$name$sj"
    }
    companion object {
        fun fromString(s: String, scope: Scope, env: Env): XcfaLabel {
            val (name, params) = Regex("(.*)\\((.*)\\)").matchEntire(s)!!.destructured
            return InvokeLabel(name, params.split(",").map { ExpressionWrapper(scope, it).instantiate(env) })
        }
    }
}

data class StartLabel(
        val name: String,
        val params: List<Expr<*>>,
        val pidVar: VarDecl<*>
) : XcfaLabel(){
    override fun toString(): String {
        val sj = StringJoiner(", ", "(", ")")
        params.forEach { sj.add(it.toString()) }
        return "$pidVar = start $name$sj"
    }
    companion object {
        fun fromString(s: String, scope: Scope, env: Env): XcfaLabel {
            val (pidVarName, name, params) = Regex("(.*) = start (.*)\\((.*)\\)").matchEntire(s)!!.destructured
            val pidVar = env.eval(scope.resolve(pidVarName).orElseThrow()) as VarDecl<*>
            return StartLabel(name, params.split(",").map { ExpressionWrapper(scope, it).instantiate(env) }, pidVar)
        }
    }
}

data class JoinLabel(
        val pid: Expr<*>
) : XcfaLabel() {
    override fun toString(): String {
        return "join $pid"
    }
    companion object {
        fun fromString(s: String, scope: Scope, env: Env): XcfaLabel {
            val (exprS) = Regex("join (.*)").matchEntire(s)!!.destructured
            return JoinLabel(ExpressionWrapper(scope, exprS).instantiate(env))
        }
    }
}

data class StmtLabel(
        val stmt: Stmt
) : XcfaLabel() {
    init {
        check(stmt !is NonDetStmt && stmt !is SequenceStmt) { "NonDetStmt and SequenceStmt are not supported in XCFA. Use the corresponding labels instead." }
    }
    override fun toStmt() : Stmt = stmt
    override fun toString(): String {
        return stmt.toString()
    }
    companion object {
        fun fromString(s: String, scope: Scope, env: Env): XcfaLabel {
           return StmtLabel(StatementWrapper(s, scope).instantiate(env))
        }
    }
}

data class ReadLabel(
        val local: VarDecl<*>,
        val global: VarDecl<*>,
        val labels: Set<String>
) : XcfaLabel() {
    override fun toString(): String {
        return "R[$local <- $global] @$labels"
    }
}

data class WriteLabel(
        val local: VarDecl<*>,
        val global: VarDecl<*>,
        val labels: Set<String>
) : XcfaLabel() {
    override fun toString(): String {
        return "W[$global <- $local] @$labels"
    }
}

data class FenceLabel(
        val labels: Set<String>
) : XcfaLabel() {
    override fun toString(): String {
        return "F[$labels]"
    }
}

data class SequenceLabel(
        val labels: List<XcfaLabel>
) : XcfaLabel() {
    override fun toStmt(): Stmt {
        return SequenceStmt(labels.map { it.toStmt() })
    }

    override fun toString(): String {
        val sj = StringJoiner(",","[","]")
        labels.forEach { sj.add(it.toString()) }
        return sj.toString()
    }
}

data class NondetLabel(
        val labels: Set<XcfaLabel>
) : XcfaLabel() {
    override fun toStmt(): Stmt {
        return NonDetStmt(labels.map { it.toStmt() })
    }
    override fun toString(): String {
        return "NonDet($labels)"
    }
}

object NopLabel : XcfaLabel() {
    override fun toStmt(): Stmt {
        return Skip()
    }

    override fun toString(): String {
        return "Nop"
    }
}