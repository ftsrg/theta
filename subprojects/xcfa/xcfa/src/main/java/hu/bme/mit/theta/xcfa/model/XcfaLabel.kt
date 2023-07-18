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
import java.util.*

sealed class XcfaLabel(open val metadata: MetaData) {

    open fun toStmt(): Stmt = Skip()
}

data class InvokeLabel @JvmOverloads constructor(
    val name: String,
    val params: List<Expr<*>>,
    override val metadata: MetaData,
    val tempLookup: Map<VarDecl<*>, VarDecl<*>> = emptyMap()
) : XcfaLabel(metadata) {

    override fun toString(): String {
        val sj = StringJoiner(", ", "(", ")")
        params.forEach { sj.add(it.toString()) }
        return "$name$sj"
    }

    companion object {

        fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
            val (name, params) = Regex("([^\\(]*)\\((.*)\\)").matchEntire(s)!!.destructured
            return InvokeLabel(name,
                params.split(",").map { ExpressionWrapper(scope, it).instantiate(env) },
                metadata = metadata)
        }
    }
}

data class ReturnLabel(val enclosedLabel: XcfaLabel) :
    XcfaLabel(metadata = enclosedLabel.metadata) {

    override fun toStmt(): Stmt {
        return enclosedLabel.toStmt()
    }

    override fun toString(): String {
        return "Return ($enclosedLabel)"
    }
}

data class StartLabel(
    val name: String,
    val params: List<Expr<*>>,
    val pidVar: VarDecl<*>,
    override val metadata: MetaData,
    val tempLookup: Map<VarDecl<*>, VarDecl<*>> = emptyMap()
) : XcfaLabel(metadata = metadata) {

    override fun toString(): String {
        val sj = StringJoiner(", ", "(", ")")
        params.forEach { sj.add(it.toString()) }
        return "$pidVar = start $name$sj"
    }

    companion object {

        fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
            val (pidVarName, pidVarType, name, params) = Regex(
                "\\(var (.*) (.*)\\) = start (.*)\\((.*)\\)").matchEntire(s)!!.destructured
            val pidVar = env.eval(scope.resolve(pidVarName).orElseThrow()) as VarDecl<*>
            return StartLabel(name,
                params.split(",").map { ExpressionWrapper(scope, it).instantiate(env) }, pidVar,
                metadata = metadata)
        }
    }
}

data class JoinLabel(
    val pidVar: VarDecl<*>,
    override val metadata: MetaData
) : XcfaLabel(metadata = metadata) {

    override fun toString(): String {
        return "join $pidVar"
    }

    companion object {

        fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
            val (pidVarName, pidVarType) = Regex("join \\(var (.*) (.*)\\)").matchEntire(
                s)!!.destructured
            val pidVar = env.eval(scope.resolve(pidVarName).orElseThrow()) as VarDecl<*>
            return JoinLabel(pidVar, metadata = metadata)
        }
    }
}

enum class ChoiceType {
    NONE,
    MAIN_PATH,
    ALTERNATIVE_PATH
}

data class StmtLabel @JvmOverloads constructor(
    val stmt: Stmt,
    val choiceType: ChoiceType = ChoiceType.NONE,
    override val metadata: MetaData
) : XcfaLabel(metadata = metadata) {

    init {
        check(
            stmt !is NonDetStmt && stmt !is SequenceStmt) { "NonDetStmt and SequenceStmt are not supported in XCFA. Use the corresponding labels instead." }
    }

    override fun toStmt(): Stmt = stmt
    override fun toString(): String {
        if (choiceType != ChoiceType.NONE)
            return "($stmt)[choiceType=$choiceType]"
        else
            return stmt.toString()
    }

    companion object {

        fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
            val matchResult = Regex("\\((.*)\\)\\[choiceType=(.*)]").matchEntire(s)
            if (matchResult != null) {
                val (stmt, choiceTypeStr) = matchResult.destructured
                return StmtLabel(StatementWrapper(stmt, scope).instantiate(env),
                    choiceType = ChoiceType.valueOf(choiceTypeStr), metadata = metadata)
            } else {
                return StmtLabel(StatementWrapper(s, scope).instantiate(env),
                    choiceType = ChoiceType.NONE, metadata = metadata)
            }
        }
    }
}

data class ReadLabel(
    val local: VarDecl<*>,
    val global: VarDecl<*>,
    val labels: Set<String>,
    override val metadata: MetaData
) : XcfaLabel(metadata = metadata) {

    override fun toString(): String {
        return "R[$local <- $global] @$labels"
    }
}

data class WriteLabel constructor(
    val local: VarDecl<*>,
    val global: VarDecl<*>,
    val labels: Set<String>,
    override val metadata: MetaData
) : XcfaLabel(metadata = metadata) {

    override fun toString(): String {
        return "W[$global <- $local] @$labels"
    }
}

data class FenceLabel(
    val labels: Set<String>,
    override val metadata: MetaData
) : XcfaLabel(metadata = metadata) {

    override fun toString(): String {
        return "F[${labels.joinToString(";")}]"
    }

    companion object {

        fun fromString(s: String, scope: Scope, env: Env, metadata: MetaData): XcfaLabel {
            val (labelList) = Regex("F\\[(.*)]").matchEntire(s)!!.destructured
            return FenceLabel(labelList.split(";").toSet(), metadata = metadata)
        }
    }
}

data class SequenceLabel @JvmOverloads constructor(
    val labels: List<XcfaLabel>,
    override val metadata: MetaData = EmptyMetaData
) : XcfaLabel(metadata = metadata) {

    override fun toStmt(): Stmt {
        return SequenceStmt(labels.map { it.toStmt() })
    }

    override fun toString(): String {
        val sj = StringJoiner(",", "[", "]")
        labels.forEach { sj.add(it.toString()) }
        return sj.toString()
    }
}

data class NondetLabel @JvmOverloads constructor(
    val labels: Set<XcfaLabel>,
    override val metadata: MetaData = EmptyMetaData
) : XcfaLabel(metadata = metadata) {

    override fun toStmt(): Stmt {
        return NonDetStmt(labels.map { it.toStmt() })
    }

    override fun toString(): String {
        return "NonDet($labels)"
    }
}

object NopLabel : XcfaLabel(metadata = EmptyMetaData) {

    override fun toStmt(): Stmt {
        return Skip()
    }

    override fun toString(): String {
        return "Nop"
    }
}

fun getTempLookup(label: XcfaLabel): Map<VarDecl<*>, VarDecl<*>> {
    return when (label) {
        is InvokeLabel -> {
            label.tempLookup
        }

        is StartLabel -> {
            label.tempLookup
        }

        is SequenceLabel -> {
            val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
            for (sublabel in label.labels) {
                lookup.putAll(getTempLookup(sublabel))
            }
            lookup
        }

        is NondetLabel -> {
            val lookup: MutableMap<VarDecl<*>, VarDecl<*>> = LinkedHashMap()
            for (sublabel in label.labels) {
                lookup.putAll(getTempLookup(sublabel))
            }
            lookup
        }

        else -> emptyMap()
    }
}