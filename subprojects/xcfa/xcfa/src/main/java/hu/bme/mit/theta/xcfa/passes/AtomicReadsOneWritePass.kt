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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * One atomic unit (atomic block or edge) can have at most one write operation on a global variable
 * and no read can happen after writing a global variable. Therefore, each atomic unit that violates
 * this rule is transformed so that each global variable is replaced with a local variable that is
 * assigned the value of the global variable at the beginning of the atomic unit and the global
 * variable is assigned the value of the local variable at the end of the atomic unit.
 */
class AtomicReadsOneWritePass : ProcedurePass {

  private lateinit var builder: XcfaProcedureBuilder

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    var indexing: VarIndexing = VarIndexingFactory.indexing(0)
    this.builder = builder

    builder.getEdges().toSet().forEach { edge ->
      if (edge.getFlatLabels().any { it is AtomicBeginLabel }) {
        val toReplace =
          edge.countAtomicBlockAccesses().mapNotNull { (v, ao) -> if (ao.wrongWrite) v else null }
        if (toReplace.isNotEmpty()) {
          val localVersions =
            toReplace.associateWith { v ->
              indexing = indexing.inc(v)
              v.localVersion(indexing)
            }

          val newStartEdge = edge.replaceAccesses(localVersions)
          val initialAssigns =
            SequenceLabel(
              localVersions.map { (v, local) ->
                StmtLabel(AssignStmt.of(cast(local, local.type), cast(v.ref, local.type)))
              }
            )
          val atomicBeginIndex =
            newStartEdge.getFlatLabels().indexOfFirst { it is AtomicBeginLabel }
          val newLabels =
            newStartEdge.getFlatLabels().toMutableList().apply {
              add(atomicBeginIndex + 1, initialAssigns)
            }
          builder.removeEdge(newStartEdge)
          builder.addEdge(newStartEdge.withLabel(SequenceLabel(newLabels)))
        }
      }
    }

    builder.getEdges().toSet().forEach { edge ->
      val toReplace =
        edge.countEdgeAccesses().mapNotNull { (v, ao) -> if (ao.wrongWrite) v else null }
      if (toReplace.isNotEmpty()) {
        val localVersions =
          toReplace.associateWith { v ->
            indexing = indexing.inc(v)
            v.localVersion(indexing)
          }
        val initialAssigns =
          localVersions.map { (v, local) ->
            StmtLabel(AssignStmt.of(cast(local, local.type), cast(v.ref, local.type)))
          }
        val newLabels = edge.getFlatLabels().map { it.replaceAccesses(localVersions) }
        val finalAssigns =
          localVersions.map { (v, local) ->
            StmtLabel(AssignStmt.of(cast(v, local.type), cast(local.ref, v.type)))
          }
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(initialAssigns + newLabels + finalAssigns)))
      }
    }
    return builder
  }

  private fun <T : Type> VarDecl<T>.localVersion(indexing: VarIndexing): VarDecl<T> =
    Decls.Var("${name}_l${indexing.get(this)}", type)

  private data class AccessOrder(var write: Boolean = false, var wrongWrite: Boolean = false)

  private fun XcfaEdge.countAtomicBlockAccesses(): Map<VarDecl<*>, AccessOrder> {
    val accesses =
      mutableMapOf<VarDecl<*>, AccessOrder>() // over-approximation of writePrecedesRead
    val toVisit = mutableListOf(this)
    while (toVisit.isNotEmpty()) {
      val current = toVisit.removeAt(0)
      var atomicEnd = false
      current.getFlatLabels().forEach {
        it.countAccesses(accesses)
        atomicEnd = atomicEnd || it is AtomicEndLabel
      }
      if (!atomicEnd) toVisit.addAll(current.target.outgoingEdges)
    }

    return accesses
  }

  private fun XcfaEdge.countEdgeAccesses(): Map<VarDecl<*>, AccessOrder> {
    val accesses = mutableMapOf<VarDecl<*>, AccessOrder>()
    getFlatLabels().forEach { it.countAccesses(accesses) }
    return accesses
  }

  private fun XcfaLabel.countAccesses(accesses: MutableMap<VarDecl<*>, AccessOrder>) {
    collectVarsWithAccessType()
      .filter { (v, _) -> v !in builder.getVars() }
      .forEach { (v, at) ->
        val t = accesses.getOrDefault(v, AccessOrder())
        if (t.write) t.wrongWrite = true
        if (at.isWritten) t.write = true
        accesses[v] = t
      }
  }

  private fun XcfaEdge.replaceAccesses(localVersions: Map<VarDecl<*>, VarDecl<*>>): XcfaEdge {
    val toVisit = mutableListOf(this)
    var first: XcfaEdge? = null
    while (toVisit.isNotEmpty()) {
      val current = toVisit.removeAt(0)
      var atomicEnd = false
      val newLabels =
        current
          .getFlatLabels()
          .map {
            atomicEnd = atomicEnd || it is AtomicEndLabel
            if (atomicEnd) it else it.replaceAccesses(localVersions)
          }
          .toMutableList()
      builder.removeEdge(current)

      if (!atomicEnd) {
        toVisit.addAll(current.target.outgoingEdges)
      } else {
        val atomicEndIndex = newLabels.indexOfFirst { it is AtomicEndLabel }
        val finalAssigns =
          SequenceLabel(
            localVersions.map { (v, local) ->
              StmtLabel(AssignStmt.of(cast(v, local.type), cast(local.ref, v.type)))
            }
          )
        newLabels.add(atomicEndIndex, finalAssigns)
      }

      val newEdge = current.withLabel(SequenceLabel(newLabels))
      builder.addEdge(newEdge)
      first = first ?: newEdge
    }
    return first!!
  }

  private fun XcfaLabel.replaceAccesses(localVersions: Map<VarDecl<*>, VarDecl<*>>): XcfaLabel {
    return when (this) {
      is StmtLabel ->
        when (val stmt = stmt) {
          is AssignStmt<*> ->
            StmtLabel(
              AssignStmt.of(
                cast(localVersions[stmt.varDecl] ?: stmt.varDecl, stmt.varDecl.type),
                cast(stmt.expr.replace(localVersions), stmt.varDecl.type),
              )
            )

          is AssumeStmt -> StmtLabel(AssumeStmt.of(stmt.cond.replace(localVersions)))
          is HavocStmt<*> -> StmtLabel(HavocStmt.of(localVersions[stmt.varDecl] ?: stmt.varDecl))
          else -> this
        }

      is SequenceLabel -> SequenceLabel(labels.map { it.replaceAccesses(localVersions) }, metadata)
      is FenceLabel -> this
      is NopLabel -> this
      else -> error("Unsupported label type at global var atomic localization: $this")
    }
  }

  private fun <T : Type> Expr<T>.replace(localVersions: Map<out Decl<*>, VarDecl<*>>): Expr<T> =
    if (this is RefExpr<T>) localVersions[decl]?.ref?.let { cast(it, decl.type) } ?: this ?: this
    else map { it.replace(localVersions) }
}
