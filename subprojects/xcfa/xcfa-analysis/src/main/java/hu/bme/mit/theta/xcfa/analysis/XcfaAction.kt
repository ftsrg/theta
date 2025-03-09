/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.algorithm.bounded.ReversibleAction
import hu.bme.mit.theta.analysis.ptr.PtrAction
import hu.bme.mit.theta.analysis.ptr.WriteTriples
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.flatten

data class XcfaAction
@JvmOverloads
constructor(
  val pid: Int,
  val edge: XcfaEdge,
  private val lastWrites: WriteTriples = emptyMap(),
  private val nextCnt: Int = 0,
) : PtrAction(lastWrites, nextCnt), ReversibleAction {

  val source: XcfaLocation = edge.source
  val target: XcfaLocation = edge.target
  val label: XcfaLabel = edge.label
  private val stmts: List<Stmt> = label.toStmt().flatten()

  constructor(
    pid: Int,
    source: XcfaLocation,
    target: XcfaLocation,
    label: XcfaLabel = NopLabel,
    metaData: MetaData = EmptyMetaData,
    lastWrites: WriteTriples = emptyMap(),
    nextCnt: Int = 0,
  ) : this(pid, XcfaEdge(source, target, label, metaData), lastWrites, nextCnt)

  override val stmtList: List<Stmt>
    get() = stmts

  override fun reverse(): ReversibleAction {
    return XcfaAction(pid, XcfaEdge(target, source, label, edge.metadata))
  }

  override fun toString(): String {
    return "$pid: $source -> $target [${getStmts()}]"
  }

  fun withLabel(sequenceLabel: SequenceLabel): XcfaAction {
    return XcfaAction(pid, source, target, sequenceLabel, edge.metadata, nextCnt = nextCnt)
  }

  fun withLastWrites(writeTriples: WriteTriples, nextCnt: Int): XcfaAction {
    return XcfaAction(pid, source, target, label, edge.metadata, writeTriples, nextCnt)
  }
}
