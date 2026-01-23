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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.model.*
import java.util.function.Predicate

fun XCFA.collectVars(): Iterable<VarDecl<*>> =
  globalVars.map { it.wrappedVar } union procedures.flatMap { it.vars }

fun XCFA.collectAssumes(): Iterable<Expr<BoolType>> =
  procedures.flatMap { procedure -> procedure.edges.flatMap { it.label.collectAssumes() } }

fun XcfaLabel.collectAssumes(): Iterable<Expr<BoolType>> =
  when (this) {
    is StmtLabel ->
      when (stmt) {
        is AssumeStmt -> setOf(stmt.cond)
        else -> setOf()
      }

    is NondetLabel -> labels.flatMap { it.collectAssumes() }
    is SequenceLabel -> labels.flatMap { it.collectAssumes() }
    else -> setOf()
  }

fun XcfaLabel.collectAssumesVars(): Set<VarDecl<*>> {
  return collectAssumes()
    .flatMap {
      val v = mutableSetOf<VarDecl<*>>()
      ExprUtils.collectVars(it, v)
      v
    }
    .toSet()
}

fun XcfaLabel.collectHavocs(): Set<HavocStmt<*>> =
  when (this) {
    is StmtLabel ->
      when (stmt) {
        is HavocStmt<*> -> setOf(stmt)
        else -> setOf()
      }

    is NondetLabel -> labels.flatMap { it.collectHavocs() }.toSet()
    is SequenceLabel -> labels.flatMap { it.collectHavocs() }.toSet()
    else -> setOf()
  }

fun XcfaLabel.collectVars(): Collection<VarDecl<*>> =
  when (this) {
    is StmtLabel -> StmtUtils.getVars(stmt)
    is NondetLabel -> labels.flatMap { it.collectVars() }
    is SequenceLabel -> labels.flatMap { it.collectVars() }
    is InvokeLabel -> params.flatMap { ExprUtils.getVars(it) }
    is JoinLabel -> setOf(pidVar)
    is StartLabel -> params.flatMap { ExprUtils.getVars(it) }.toSet() union setOf(pidVar)
    is FenceLabel ->
      when (this) {
        is AtomicFenceLabel -> setOf()
        is MutexTryLockLabel -> setOf(handle, successVar)
        else -> setOf(handle)
      }
    else -> emptySet()
  }

// Complex var access requests

typealias AccessType = Pair<Boolean, Boolean>

typealias VarAccessMap = Map<VarDecl<*>, AccessType>

typealias DereferenceAccessMap = Map<Dereference<*, *, *>, AccessType>

typealias GlobalVarAccessMap = Map<XcfaGlobalVar, AccessType>

val AccessType?.isRead
  get() = this?.first == true
val AccessType?.isWritten
  get() = this?.second == true

fun AccessType?.merge(other: AccessType?) =
  Pair(this?.first == true || other?.first == true, this?.second == true || other?.second == true)

val WRITE: AccessType
  get() = Pair(false, true)
val READ: AccessType
  get() = Pair(true, false)

private fun List<VarAccessMap>.mergeVarAccesses(): VarAccessMap =
  this.fold(mapOf()) { acc, next ->
    (acc.keys + next.keys).associateWith { acc[it].merge(next[it]) }
  }

private fun List<DereferenceAccessMap>.mergeDerefs(): DereferenceAccessMap =
  this.fold(mapOf()) { acc, next ->
    (acc.keys + next.keys).associateWith { acc[it].merge(next[it]) }
  }

/** Returns the list of accessed variables by the edge associated with an AccessType object. */
fun XcfaEdge.collectVarsWithAccessType(): VarAccessMap = label.collectVarsWithAccessType()

/**
 * Returns the list of accessed variables by the label. The variable is associated with an
 * AccessType object based on whether the variable is read/written by the label.
 */
fun XcfaLabel.collectVarsWithAccessType(): VarAccessMap =
  when (this) {
    is StmtLabel -> {
      when (stmt) {
        is HavocStmt<*> -> mapOf(stmt.varDecl to WRITE)
        is AssignStmt<*> ->
          ExprUtils.getVars(stmt.expr).associateWith { READ } + mapOf(stmt.varDecl to WRITE)

        else -> StmtUtils.getVars(stmt).associateWith { READ }
      }
    }

    is NondetLabel -> labels.map { it.collectVarsWithAccessType() }.mergeVarAccesses()
    is SequenceLabel -> labels.map { it.collectVarsWithAccessType() }.mergeVarAccesses()
    is InvokeLabel ->
      params.flatMap { ExprUtils.getVars(it) }.associateWith { READ } // TODO is it read?
    is StartLabel ->
      params.flatMap { ExprUtils.getVars(it) }.associateWith { READ } + mapOf(pidVar to WRITE)

    is JoinLabel -> mapOf(pidVar to READ)
    is FenceLabel -> {
      when (this) {
        is AtomicFenceLabel -> mapOf()
        is MutexTryLockLabel -> mapOf(handle to READ) + mapOf(successVar to WRITE)
        else -> mapOf(handle to READ)
      }
    }
    else -> emptyMap()
  }

/**
 * Returns the global variables accessed by the label (the variables present in the given argument).
 */
fun XcfaLabel.collectGlobalVars(globalVars: Set<XcfaGlobalVar>): GlobalVarAccessMap =
  collectVarsWithAccessType()
    .mapNotNull { labelVar ->
      globalVars.firstOrNull { it.wrappedVar == labelVar.key }?.let { Pair(it, labelVar.value) }
    }
    .toMap()

/**
 * Returns the global variables (potentially indirectly) accessed by the edge. If the edge starts an
 * atomic block, all variable accesses in the atomic block are returned. Variables are associated
 * with a pair of boolean values: the first is true if the variable is read and false otherwise. The
 * second is similar for write access.
 */
fun XcfaEdge.collectIndirectGlobalVarAccesses(xcfa: XCFA): GlobalVarAccessMap {
  val globalVars = xcfa.globalVars
  val flatLabels = getFlatLabels()
  val mutexes =
    flatLabels.filterIsInstance<FenceLabel>().flatMap { it.acquiredMutexes }.toMutableSet()
  return if (mutexes.isEmpty()) {
    label.collectGlobalVars(globalVars)
  } else {
    collectGlobalVarsWithTraversal(globalVars) { it.mutexOperations(mutexes) }
  }
}

/**
 * Returns global variables encountered in a search starting from the edge.
 *
 * @param goFurther the predicate that tells whether more edges have to be explored through an edge
 * @return the set of encountered shared objects
 */
private fun XcfaEdge.collectGlobalVarsWithTraversal(
  globalVars: Set<XcfaGlobalVar>,
  goFurther: Predicate<XcfaEdge>,
): GlobalVarAccessMap {
  val vars = mutableMapOf<XcfaGlobalVar, AccessType>()
  val exploredEdges = mutableListOf<XcfaEdge>()
  val edgesToExplore = mutableListOf<XcfaEdge>()
  edgesToExplore.add(this)
  while (edgesToExplore.isNotEmpty()) {
    val exploring = edgesToExplore.removeFirst()
    exploring.label.collectGlobalVars(globalVars).forEach { (varDecl, access) ->
      vars[varDecl] = vars[varDecl].merge(access)
    }
    if (goFurther.test(exploring)) {
      for (newEdge in exploring.target.outgoingEdges) {
        if (newEdge !in exploredEdges) {
          edgesToExplore.add(newEdge)
        }
      }
    }
    exploredEdges.add(exploring)
  }
  return vars
}

// (De)reference collection

val XcfaLabel.references: List<Reference<*, *>>
  get() =
    when (this) {
      is StmtLabel ->
        when (stmt) {
          is AssumeStmt -> stmt.cond.references
          is AssignStmt<*> -> stmt.expr.references
          is MemoryAssignStmt<*, *, *> -> stmt.deref.references + stmt.expr.references
          else -> emptyList()
        }

      is InvokeLabel -> params.flatMap { it.references }
      is NondetLabel -> labels.flatMap { it.references }
      is SequenceLabel -> labels.flatMap { it.references }
      is StartLabel -> params.flatMap { it.references }
      else -> emptyList()
    }

val Expr<*>.references: List<Reference<*, *>>
  get() =
    if (this is Reference<*, *>) {
      listOf(this) + this.ops.flatMap { it.references }
    } else {
      ops.flatMap { it.references }
    }

val XcfaLabel.dereferences: List<Dereference<*, *, *>>
  get() =
    when (this) {
      is StmtLabel -> stmt.dereferences
      is InvokeLabel -> params.flatMap { it.dereferences }
      is NondetLabel -> labels.flatMap { it.dereferences }
      is SequenceLabel -> labels.flatMap { it.dereferences }
      is StartLabel -> params.flatMap { it.dereferences }
      else -> emptyList()
    }

val Stmt.dereferences: List<Dereference<*, *, *>>
  get() =
    when (this) {
      is AssumeStmt -> cond.dereferences
      is AssignStmt<*> -> expr.dereferences
      is MemoryAssignStmt<*, *, *> -> deref.dereferences + expr.dereferences
      else -> emptyList()
    }

val Expr<*>.dereferences: List<Dereference<*, *, *>>
  get() =
    if (this is Dereference<*, *, *>) {
      ops.flatMap { it.dereferences } + listOf(this)
    } else {
      ops.flatMap { it.dereferences }
    }

val XcfaLabel.dereferencesWithAccessType: DereferenceAccessMap
  get() =
    when (this) {
      is NondetLabel -> error("NondetLabel is not well-defined for dereferences due to ordering")
      is SequenceLabel -> labels.map(XcfaLabel::dereferencesWithAccessType).mergeDerefs()
      is InvokeLabel -> params.map { it.dereferences.associateWith { READ } }.mergeDerefs()
      is StartLabel -> params.map { it.dereferences.associateWith { READ } }.mergeDerefs()
      is StmtLabel -> stmt.dereferencesWithAccessType
      else -> mapOf()
    }

val Stmt.dereferencesWithAccessType: DereferenceAccessMap
  get() =
    when (this) {
      is MemoryAssignStmt<*, *, *> ->
        listOfNotNull(
            mapOf(deref to WRITE),
            (deref.dereferences - deref).associateWith { READ },
            expr.dereferences.associateWith { READ },
          )
          .mergeDerefs()

      is AssignStmt<*> -> expr.dereferences.associateWith { READ }
      is AssumeStmt -> cond.dereferences.associateWith { READ }
      else -> mapOf()
    }
