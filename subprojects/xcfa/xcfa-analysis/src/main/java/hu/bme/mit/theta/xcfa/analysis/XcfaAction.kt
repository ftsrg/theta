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

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrAction
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.ptr.WriteTriples
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.flatten

data class XcfaAction(val pid: Int, val edge: XcfaEdge, val state: XcfaState<out PtrState<out ExprState>>) :
    PtrAction(state.sGlobal.lastWrites, state.sGlobal.nextCnt) {

    val source: XcfaLocation = edge.source
    val target: XcfaLocation = edge.target
    val label: XcfaLabel = edge.label
    private val stmts: List<Stmt> = label.toStmt().flatten()

    constructor(pid: Int, source: XcfaLocation, target: XcfaLocation,
        label: XcfaLabel = NopLabel, state: XcfaState<out PtrState<out ExprState>>) : this(pid,
        XcfaEdge(source, target, label),
        state)

    override val stmtList: List<Stmt>
        get() = stmts

    override fun toString(): String {
        return "$pid: $source -> $target [${getStmts()}]"
    }

    fun withLabel(sequenceLabel: SequenceLabel): XcfaAction {
        return XcfaAction(pid, source, target, sequenceLabel, state)
    }

    fun withLastWrites(writeTriples: WriteTriples): XcfaAction {
        val state = this.state as XcfaState<PtrState<*>>
        return XcfaAction(pid, source, target, label, state.copy(sGlobal = state.sGlobal.withLastWrites(writeTriples)))
    }

}
