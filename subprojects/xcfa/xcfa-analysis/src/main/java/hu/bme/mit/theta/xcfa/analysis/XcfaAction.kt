/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.flatten
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten

data class XcfaAction
@JvmOverloads
constructor(
  val pid: Int,
  val edge: XcfaEdge,
  private val lastWrites: WriteTriples = emptyMap(),
  private val nextCnt: Int = 0,
) : PtrAction(lastWrites, nextCnt), ReversibleAction {

  /**
   * The values the havocs of [label] took, in flat label order, as far as the backend knows them
   * (null where it does not). Only a hint for the trace concretizer, so it is not part of equality.
   */
  var inputs: List<LitExpr<*>?>? = null
    private set

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
    return XcfaAction(pid, source, target, sequenceLabel, edge.metadata, lastWrites, nextCnt)
  }

  fun withLastWrites(writeTriples: WriteTriples, nextCnt: Int): XcfaAction {
    return XcfaAction(pid, edge, writeTriples, nextCnt).withInputs(inputs)
  }

  fun withInputs(inputs: List<LitExpr<*>?>?): XcfaAction {
    return XcfaAction(pid, edge, lastWrites, nextCnt).also { it.inputs = inputs }
  }

  /**
   * The values of this action's havocs that [post], a valuation after the action, determines: that
   * of each havoc whose variable no later label of the action writes.
   */
  fun inputsFrom(post: Valuation): List<LitExpr<*>?> {
    val writtenLater = mutableSetOf<VarDecl<*>>()
    val values = ArrayDeque<LitExpr<*>?>()
    for (flat in label.getFlatLabels().asReversed()) {
      val stmt = (flat as? StmtLabel)?.stmt
      if (stmt is HavocStmt<*>) {
        values.addFirst(
          if (stmt.varDecl in writtenLater) null else post.eval(stmt.varDecl).orElse(null)
        )
        writtenLater.add(stmt.varDecl)
      } else if (stmt != null) {
        writtenLater.addAll(StmtUtils.getWrittenVars(stmt))
      } else {
        writtenLater.addAll(flat.collectVarsWithAccessType().filter { it.value.isWritten }.keys)
      }
    }
    return values.toList()
  }
}
