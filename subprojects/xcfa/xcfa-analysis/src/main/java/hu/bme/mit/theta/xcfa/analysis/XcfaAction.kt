/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.flatten

data class XcfaAction(val pid: Int, val edge: XcfaEdge) : StmtAction() {

    val source: XcfaLocation = edge.source
    val target: XcfaLocation = edge.target
    val label: XcfaLabel = edge.label.uniqueDereferences()
    private val stmts: List<Stmt> = label.toStmt().flatten()

    constructor(pid: Int, source: XcfaLocation, target: XcfaLocation,
        label: XcfaLabel = NopLabel) : this(pid, XcfaEdge(source, target, label))

    override fun getStmts(): List<Stmt> {
        return stmts
    }

    override fun toString(): String {
        return "$pid: $source -> $target [$label]"
    }

    fun withLabel(sequenceLabel: SequenceLabel): XcfaAction {
        return XcfaAction(pid, source, target, sequenceLabel)
    }


}

private fun XcfaLabel.uniqueDereferences(): XcfaLabel = when (this) {
    is NondetLabel -> NondetLabel(labels.map(XcfaLabel::uniqueDereferences).toSet(), metadata)
    is SequenceLabel -> SequenceLabel(labels.map(XcfaLabel::uniqueDereferences), metadata)
    is InvokeLabel -> InvokeLabel(name, params.map(Expr<*>::uniqueDereferences), metadata, tempLookup)
    is StartLabel -> StartLabel(name, params.map(Expr<*>::uniqueDereferences), pidVar, metadata, tempLookup)
    is StmtLabel -> StmtLabel(when (stmt) {
        is MemoryAssignStmt<*, *> -> MemoryAssignStmt.create(
            (stmt as MemoryAssignStmt<*, *>).deref.uniqueDereferences() as Dereference<*, *>,
            (stmt as MemoryAssignStmt<*, *>).expr.uniqueDereferences())

        is AssignStmt<*> -> AssignStmt.of(cast((stmt as AssignStmt<*>).varDecl, (stmt as AssignStmt<*>).varDecl.type),
            cast((stmt as AssignStmt<*>).expr.uniqueDereferences(), (stmt as AssignStmt<*>).varDecl.type))

        is AssumeStmt -> AssumeStmt.of((stmt as AssumeStmt).cond.uniqueDereferences() as Expr<BoolType>)
        else -> stmt
    }, choiceType, metadata)

    else -> this
}

private fun Expr<*>.uniqueDereferences(): Expr<*> = if (this is Dereference<*, *> && this.uniquenessIdx.isEmpty) {
    this.withOps(this.withFreshVar().ops.map(Expr<*>::uniqueDereferences))
} else {
    this.withOps(this.ops.map(Expr<*>::uniqueDereferences))
}
