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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.Expr
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
}

data class JoinLabel(
        val pid: Expr<*>
) : XcfaLabel() {
    override fun toString(): String {
        return "join $pid"
    }
}

data class StmtLabel(
        val stmt: Stmt
) : XcfaLabel() {
    override fun toStmt() : Stmt = stmt
    override fun toString(): String {
        return stmt.toString()
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
        return labels.toString()
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