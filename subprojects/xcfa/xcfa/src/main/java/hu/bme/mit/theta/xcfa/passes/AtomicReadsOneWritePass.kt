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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
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
      // Only a block left open at the end of the edge spans edges; one closed within the edge (e.g.
      // the checked writes of SpinLoopEffectPass) is part of the edge's unit, handled below.
      if (edge.openAtomicBlockStart() >= 0) {
        val toReplace =
          edge.countAtomicBlockAccesses().mapNotNull { (v, ao) -> if (ao.wrongWrite) v else null }
        if (toReplace.isNotEmpty()) {
          val localVersions =
            toReplace.associateWith { v ->
              indexing = indexing.inc(v)
              v.localVersion(indexing, builder)
            }

          // The edge is atomic with the block it opens, so its labels before the begin are
          // localized too, and the copy-in has to precede the first of them that accesses a
          // localized variable. A leading branch guard stays first (see the prefix below).
          val oldLabels = edge.getFlatLabels()
          val copyInIndex =
            if (oldLabels.take(edge.openAtomicBlockStart()).none { it.accesses(toReplace) })
              edge.openAtomicBlockStart() + 1
            else oldLabels.takeWhile { it.isAssume() && !it.accesses(toReplace) }.size
          val newStartEdge = edge.replaceAccesses(localVersions)
          val initialAssigns =
            SequenceLabel(
              localVersions
                .filter { (v, _) -> !oldLabels.writtenBeforeRead(v) }
                .map { (v, local) ->
                  StmtLabel(AssignStmt.of(cast(local, local.type), cast(v.ref, local.type)))
                }
            )
          val newLabels =
            newStartEdge.getFlatLabels().toMutableList().apply { add(copyInIndex, initialAssigns) }
          builder.removeEdge(newStartEdge)
          builder.addEdge(newStartEdge.withLabel(SequenceLabel(newLabels)))
        }
      }
    }

    // A branching location's outgoing edges must each start with an assume (the OC backend requires
    // it). When the leading guard *itself* reads a variable that has to be localized, the copy-in
    // cannot be placed in front of it on the same edge, and the `prefix` mitigation below computes
    // 0. Hoist the copy-in onto a new edge *above* the branch instead, shared by every sibling.
    //
    // It has to cover every outgoing edge with one shared local, not just the edge that needs it:
    // the OC encoding ties sibling branch conditions together through the declaration they read
    // (`assumeConsts` in XcfaToEventGraph), so localizing one branch while its siblings keep
    // reading
    // the global unties them and lets the two branches disagree about the value of the same global
    // -- a false race, not a crash. Hoisting gives a single read of the global that all the guards
    // share, which preserves the tie.
    //
    // This is exactly the shape DataRaceToReachabilityPass produces: `assume(assertion); set;
    // access; unset` on the MAIN_PATH edge (so the flag is written twice -> wrongWrite) against
    // `assume(!assertion)` on the ALTERNATIVE_PATH sibling, which only reads the same flags.
    val hoistedAway = mutableSetOf<XcfaEdge>()
    builder.getLocs().toSet().forEach { source ->
      val outgoing = source.outgoingEdges.toSet()
      if (outgoing.size <= 1) return@forEach
      val perEdge = outgoing.associateWith { it.wrongWriteVars() }
      val blocked =
        perEdge.any { (e, tr) ->
          tr.isNotEmpty() &&
            e.getFlatLabels().firstOrNull().let { first ->
              first is StmtLabel &&
                first.stmt is AssumeStmt &&
                first.collectVarsWithAccessType(builder).any { (v, _) -> v in tr }
            }
        }
      if (!blocked) return@forEach
      val shared = perEdge.values.flatten().toSet()
      if (shared.isEmpty()) return@forEach

      val localVersions =
        shared.associateWith { v ->
          indexing = indexing.inc(v)
          v.localVersion(indexing, builder)
        }
      val branchLoc =
        XcfaLocation(
          "${source.name}_dr_local${XcfaLocation.uniqueCounter()}",
          metadata = source.metadata,
        )
      builder.addLoc(branchLoc)
      outgoing.forEach { e ->
        // Write the local back only on the branches that actually modify it: an unconditional
        // write-back would add a spurious write event to the global on a read-only branch.
        val written = e.collectVarsWithAccessType(builder).any { (v, at) -> v in shared && at.isWritten }
        val newLabels = e.getFlatLabels().map { it.replaceAccesses(localVersions) }
        val finalAssigns =
          if (!written) listOf()
          else
            localVersions.map { (v, local) ->
              StmtLabel(AssignStmt.of(cast(v, local.type), cast(local.ref, v.type)))
            }
        builder.removeEdge(e)
        val moved =
          XcfaEdge(branchLoc, e.target, SequenceLabel(newLabels + finalAssigns), e.metadata)
        builder.addEdge(moved)
        hoistedAway.add(moved)
      }
      builder.addEdge(
        XcfaEdge(
          source,
          branchLoc,
          SequenceLabel(
            localVersions.map { (v, local) ->
              StmtLabel(AssignStmt.of(cast(local, local.type), cast(v.ref, local.type)))
            }
          ),
          EmptyMetaData,
        )
      )
    }

    builder.getEdges().toSet().forEach { edge ->
      if (edge in hoistedAway) return@forEach
      val toReplace = edge.wrongWriteVars()
      if (toReplace.isNotEmpty()) {
        val localVersions =
          toReplace.associateWith { v ->
            indexing = indexing.inc(v)
            v.localVersion(indexing, builder)
          }
        val oldLabels = edge.getFlatLabels()
        val initialAssigns =
          localVersions
            .filter { (v, _) -> !oldLabels.writtenBeforeRead(v) }
            .map { (v, local) ->
              StmtLabel(AssignStmt.of(cast(local, local.type), cast(v.ref, local.type)))
            }
        val newLabels = oldLabels.map { it.replaceAccesses(localVersions) }
        val finalAssigns =
          localVersions.map { (v, local) ->
            StmtLabel(AssignStmt.of(cast(v, local.type), cast(local.ref, v.type)))
          }
        // The OC backend requires every outgoing edge of a branching location to start with an
        // assume. Prepending the local copy-in (initialAssigns) in front of a leading branch-guard
        // assume would violate that. Keep the leading assume(s) first and insert the copy-in right
        // after them -- safe because such guards do not touch a localized variable (they have no
        // accesses to `toReplace`), so reading the global into the local before or after them
        // yields the same value.
        val prefix =
          oldLabels
            .takeWhile { label ->
              label is StmtLabel &&
                label.stmt is AssumeStmt &&
                label.collectVarsWithAccessType(builder).none { (v, _) -> v in toReplace }
            }
            .size
        builder.removeEdge(edge)
        builder.addEdge(
          edge.withLabel(
            SequenceLabel(
              newLabels.subList(0, prefix) +
                initialAssigns +
                newLabels.subList(prefix, newLabels.size) +
                finalAssigns
            )
          )
        )
      }
    }
    return builder
  }

  /**
   * The index of the begin of the atomic block that is still open at the end of this edge, or -1 if
   * every block it begins also ends in it.
   */
  private fun XcfaEdge.openAtomicBlockStart(): Int {
    val labels = getFlatLabels()
    val lastFence = labels.indexOfLast { it is AtomicBeginLabel || it is AtomicEndLabel }
    return if (lastFence >= 0 && labels[lastFence] is AtomicBeginLabel) lastFence else -1
  }

  /**
   * Whether the first of these labels that accesses [v] overwrites it without reading it. The
   * copy-in is then dead, and harmful: it reads the global before its first write -- e.g. in the
   * initialization of the entry thread, where no write precedes it, so the read could only read
   * from another thread's later write, and every execution became infeasible.
   */
  private fun List<XcfaLabel>.writtenBeforeRead(v: VarDecl<*>): Boolean {
    val first = firstOrNull { it.accesses(listOf(v)) } as? StmtLabel ?: return false
    return when (val stmt = first.stmt) {
      is HavocStmt<*> -> stmt.varDecl == v
      is AssignStmt<*> -> stmt.varDecl == v && v !in ExprUtils.getVars(stmt.expr)
      else -> false
    }
  }

  private fun XcfaLabel.isAssume() = this is StmtLabel && stmt is AssumeStmt

  private fun XcfaLabel.accesses(vars: Collection<VarDecl<*>>) =
    collectVarsWithAccessType().any { (v, _) -> v in vars }

  private fun <T : Type> VarDecl<T>.localVersion(
    indexing: VarIndexing,
    builder: XcfaProcedureBuilder,
  ): VarDecl<T> = Decls.Var("${name}_l${indexing.get(this)}", type).also { builder.addVar(it) }

  private data class AccessOrder(var write: Boolean = false, var wrongWrite: Boolean = false)

  private fun XcfaEdge.countAtomicBlockAccesses(): Map<VarDecl<*>, AccessOrder> {
    val accesses =
      mutableMapOf<VarDecl<*>, AccessOrder>() // over-approximation of writePrecedesRead
    atomicBlockEdges().forEach { (edge, _) ->
      edge.getFlatLabels().forEach { it.countAccesses(accesses) }
    }
    return accesses
  }

  /**
   * The edges of the atomic block this edge leaves open, each once (a location where branches of
   * the block join is reached on several paths), with the index of the label ending the block, or
   * -1 on the edges the block continues past.
   */
  private fun XcfaEdge.atomicBlockEdges(): List<Pair<XcfaEdge, Int>> {
    val visited = mutableSetOf(this)
    val toVisit = mutableListOf(this)
    val result = mutableListOf<Pair<XcfaEdge, Int>>()
    while (toVisit.isNotEmpty()) {
      val current = toVisit.removeAt(0)
      val start = if (current === this) openAtomicBlockStart() else -1
      val end =
        current
          .getFlatLabels()
          .withIndex()
          .firstOrNull { (i, it) -> it is AtomicEndLabel && i > start }
          ?.index ?: -1
      result.add(current to end)
      if (end < 0) current.target.outgoingEdges.filter(visited::add).let(toVisit::addAll)
    }
    return result
  }

  /** The variables this edge reads or writes *after* having written them (see [AccessOrder]). */
  private fun XcfaEdge.wrongWriteVars(): List<VarDecl<*>> =
    countEdgeAccesses().mapNotNull { (v, ao) -> if (ao.wrongWrite) v else null }

  private fun XcfaEdge.countEdgeAccesses(): Map<VarDecl<*>, AccessOrder> {
    val accesses = mutableMapOf<VarDecl<*>, AccessOrder>()
    getFlatLabels().forEach { it.countAccesses(accesses) }
    return accesses
  }

  private fun XcfaLabel.countAccesses(accesses: MutableMap<VarDecl<*>, AccessOrder>) {
    collectVarsWithAccessType(builder)
      .filter { (v, _) -> v !in builder.getVars() }
      .forEach { (v, at) ->
        val t = accesses.getOrDefault(v, AccessOrder())
        if (t.write) t.wrongWrite = true
        if (at.isWritten) t.write = true
        accesses[v] = t
      }
  }

  private fun XcfaEdge.replaceAccesses(localVersions: Map<VarDecl<*>, VarDecl<*>>): XcfaEdge =
    atomicBlockEdges()
      .map { (current, end) ->
        val newLabels =
          current
            .getFlatLabels()
            .mapIndexed { i, it -> if (end in 0..<i) it else it.replaceAccesses(localVersions) }
            .toMutableList()
        if (end >= 0) {
          newLabels.add(
            end,
            SequenceLabel(
              localVersions.map { (v, local) ->
                StmtLabel(AssignStmt.of(cast(v, local.type), cast(local.ref, v.type)))
              }
            ),
          )
        }
        builder.removeEdge(current)
        current.withLabel(SequenceLabel(newLabels)).also(builder::addEdge)
      }
      .first()

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
          is MemoryAssignStmt<*, *, *> ->
            StmtLabel(
              MemoryAssignStmt.create(
                stmt.deref.replace(localVersions) as Dereference<*, *, *>,
                stmt.expr.replace(localVersions),
              )
            )
          else -> {
            check(!accesses(localVersions.keys)) {
              "Unsupported statement at global var atomic localization: $this"
            }
            this
          }
        }

      is SequenceLabel -> SequenceLabel(labels.map { it.replaceAccesses(localVersions) }, metadata)
      is StartLabel ->
        copy(
          params = params.map { it.replace(localVersions) },
          pidVar = localVersions[pidVar] ?: pidVar,
        )
      is FenceLabel -> this
      is NopLabel -> this
      else -> error("Unsupported label type at global var atomic localization: $this")
    }
  }

  private fun <T : Type> Expr<T>.replace(localVersions: Map<out Decl<*>, VarDecl<*>>): Expr<T> =
    if (this is RefExpr<T>) localVersions[decl]?.ref?.let { cast(it, decl.type) } ?: this ?: this
    else map { it.replace(localVersions) }
}
