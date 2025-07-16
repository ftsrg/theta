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
package hu.bme.mit.theta.xcfa

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.common.Try
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtSimplifier
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import java.util.function.Predicate

/** Get flattened label list (without sequence labels). */
fun XcfaEdge.getFlatLabels(): List<XcfaLabel> = label.getFlatLabels()

fun XcfaLabel.getFlatLabels(): List<XcfaLabel> =
  when (this) {
    is SequenceLabel -> {
      val ret = mutableListOf<XcfaLabel>()
      labels.forEach { ret.addAll(it.getFlatLabels()) }
      ret
    }

    else -> listOf(this)
  }

fun XCFA.collectVars(): Iterable<VarDecl<*>> =
  globalVars.map { it.wrappedVar } union procedures.map { it.vars }.flatten()

fun XCFA.collectAssumes(): Iterable<Expr<BoolType>> =
  procedures
    .map { procedure -> procedure.edges.map { it.label.collectAssumes() }.flatten() }
    .flatten()

fun XcfaLabel.collectAssumes(): Iterable<Expr<BoolType>> =
  when (this) {
    is StmtLabel ->
      when (stmt) {
        is AssumeStmt -> setOf(stmt.cond)
        else -> setOf()
      }

    is NondetLabel -> labels.map { it.collectAssumes() }.flatten()
    is SequenceLabel -> labels.map { it.collectAssumes() }.flatten()
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

    is NondetLabel -> labels.map { it.collectHavocs() }.flatten().toSet()
    is SequenceLabel -> labels.map { it.collectHavocs() }.flatten().toSet()
    else -> setOf()
  }

fun XcfaLabel.collectVars(): Iterable<VarDecl<*>> =
  when (this) {
    is StmtLabel -> StmtUtils.getVars(stmt)
    is NondetLabel -> labels.map { it.collectVars() }.flatten()
    is SequenceLabel -> labels.map { it.collectVars() }.flatten()
    is InvokeLabel -> params.map { ExprUtils.getVars(it) }.flatten()
    is JoinLabel -> setOf(pidVar)
    is ReadLabel -> setOf(global, local)
    is StartLabel -> params.map { ExprUtils.getVars(it) }.flatten().toSet() union setOf(pidVar)
    is WriteLabel -> setOf(global, local)
    else -> emptySet()
  }

// Complex var access requests

typealias AccessType = Pair<Boolean, Boolean>

typealias VarAccessMap = Map<VarDecl<*>, AccessType>

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

private fun List<VarAccessMap>.mergeAndCollect(): VarAccessMap =
  this.fold(mapOf()) { acc, next ->
    (acc.keys + next.keys).associateWith { acc[it].merge(next[it]) }
  }

private operator fun VarAccessMap?.plus(other: VarAccessMap?): VarAccessMap =
  listOfNotNull(this, other).mergeAndCollect()

inline val XcfaLabel.isAtomicBegin: Boolean
  get() = this is FenceLabel && "ATOMIC_BEGIN" in labels
inline val XcfaLabel.isAtomicEnd: Boolean
  get() = this is FenceLabel && "ATOMIC_END" in labels

/** The set of mutexes acquired by the label. */
inline val FenceLabel.acquiredMutexes: Set<String>
  get() = labels.mapNotNull { it.acquiredMutex }.toSet()

inline val String.acquiredMutex: String?
  get() =
    when {
      this == "ATOMIC_BEGIN" -> ""
      startsWith("mutex_lock") -> substringAfter('(').substringBefore(')')
      startsWith("cond_wait") -> substring("cond_wait".length + 1, length - 1).split(",")[1]
      else -> null
    }

/** The set of mutexes released by the label. */
inline val FenceLabel.releasedMutexes: Set<String>
  get() = labels.mapNotNull { it.releasedMutex }.toSet()

inline val String.releasedMutex: String?
  get() =
    when {
      this == "ATOMIC_END" -> ""
      startsWith("mutex_unlock") -> substringAfter('(').substringBefore(')')
      startsWith("start_cond_wait") ->
        substring("start_cond_wait".length + 1, length - 1).split(",")[1]
      else -> null
    }

/** The set of mutexes acquired embedded into each other. */
inline val XcfaEdge.acquiredEmbeddedFenceVars: Set<String>
  get() {
    val acquired = mutableSetOf<String>()
    val toVisit = mutableListOf<Pair<XcfaEdge, Set<String>>>(this to setOf())
    while (toVisit.isNotEmpty()) {
      val (visiting, mutexes) = toVisit.removeAt(0)
      val newMutexes = mutexes.toMutableSet()
      acquired.addAll(
        visiting.getFlatLabels().flatMap { fence ->
          if (fence !is FenceLabel) return@flatMap emptyList()
          fence.acquiredMutexes +
            fence.labels
              .filter { it.startsWith("start_cond_wait") }
              .map { it.substring("start_cond_wait".length + 1, it.length - 1).split(",")[0] }
        }
      )
      if (visiting.mutexOperations(newMutexes)) {
        visiting.target.outgoingEdges.forEach { toVisit.add(it to newMutexes) }
      }
    }
    return acquired
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
        is MemoryAssignStmt<*, *, *> -> {
          var expr: Expr<*> = stmt.deref
          while (expr is Dereference<*, *, *>) {
            expr = expr.array
          }
          ExprUtils.getVars(stmt.expr).associateWith { READ } +
            when (expr) {
              is RefExpr<*> ->
                mapOf(expr.decl as VarDecl<*> to READ) // the memory address is read, not written
              is LitExpr<*> -> mapOf()
              else -> error("MemoryAssignStmts's dereferences should only contain refs or lits")
            }
        }

        else -> StmtUtils.getVars(stmt).associateWith { READ }
      }
    }

    is NondetLabel -> labels.map { it.collectVarsWithAccessType() }.mergeAndCollect()
    is SequenceLabel -> labels.map { it.collectVarsWithAccessType() }.mergeAndCollect()
    is InvokeLabel ->
      params.map { ExprUtils.getVars(it) }.flatten().associateWith { READ } // TODO is it read?
    is StartLabel ->
      params.map { ExprUtils.getVars(it) }.flatten().associateWith { READ } + mapOf(pidVar to READ)
    is JoinLabel -> mapOf(pidVar to READ)
    is ReadLabel -> mapOf(global to READ, local to READ)
    is WriteLabel -> mapOf(global to WRITE, local to WRITE)
    else -> emptyMap()
  }

/**
 * Returns the global variables accessed by the label (the variables present in the given argument).
 */
private fun XcfaLabel.collectGlobalVars(globalVars: Set<XcfaGlobalVar>): GlobalVarAccessMap =
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
 * Represents a global variable access: stores the variable declaration, the access type
 * (read/write) and the set of mutexes that are needed to perform the variable access.
 */
class GlobalVarAccessWithMutexes(
  val globalVar: XcfaGlobalVar,
  val access: AccessType,
  val mutexes: Set<String>,
)

/**
 * Returns the global variable accesses of the edge.
 *
 * @param xcfa the XCFA that contains the edge
 * @param currentMutexes the set of mutexes currently acquired by the process of the edge
 * @return the list of global variable accesses (c.f., [GlobalVarAccessWithMutexes])
 */
fun XcfaEdge.getGlobalVarsWithNeededMutexes(
  xcfa: XCFA,
  currentMutexes: Set<String>,
): List<GlobalVarAccessWithMutexes> {
  val globalVars = xcfa.globalVars
  val neededMutexes = currentMutexes.toMutableSet()
  val accesses = mutableListOf<GlobalVarAccessWithMutexes>()
  getFlatLabels().forEach { label ->
    if (label is FenceLabel) {
      neededMutexes.addAll(label.acquiredMutexes)
    } else {
      val vars = label.collectGlobalVars(globalVars)
      accesses.addAll(
        vars.mapNotNull { (varDecl, accessType) ->
          if (
            accesses.any {
              it.globalVar == varDecl && (it.access == accessType && it.access == WRITE)
            }
          ) {
            null
          } else {
            GlobalVarAccessWithMutexes(varDecl, accessType, neededMutexes.toSet())
          }
        }
      )
    }
  }
  return accesses
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
    val exploring = edgesToExplore.removeAt(0)
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

/**
 * Follows the mutex operations of the given edge and updates the given set of mutexes.
 *
 * @param mutexes the set of mutexes currently acquired
 * @return true if the set of mutexes is non-empty after the mutex operations
 */
fun XcfaEdge.mutexOperations(mutexes: MutableSet<String>): Boolean {
  val edgeFlatLabels = getFlatLabels()
  val acquiredLocks = mutableSetOf<String>()
  val releasedLocks = mutableSetOf<String>()
  edgeFlatLabels.filterIsInstance<FenceLabel>().forEach { fence ->
    releasedLocks.addAll(fence.releasedMutexes)
    acquiredLocks.removeAll(fence.releasedMutexes)

    acquiredLocks.addAll(fence.acquiredMutexes)
    releasedLocks.removeAll(fence.acquiredMutexes)
  }
  mutexes.removeAll(releasedLocks)
  mutexes.addAll(acquiredLocks)
  return mutexes.isNotEmpty()
}

fun XCFA.getSymbols(): Pair<XcfaScope, Env> {
  val symbolTable = SymbolTable()
  val scope = XcfaScope(symbolTable)
  val vars = collectVars()
  val env = Env()
  vars.forEach {
    val symbol = Symbol { it.name }
    symbolTable.add(symbol)
    env.define(symbol, it)
  }
  return Pair(scope, env)
}

/**
 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an
 * AtomicBegin and before an edge with an AtomicEnd).
 *
 * @param builder the atomic block inner locations of the procedure of this builder will be returned
 * @return the list of locations in an atomic block
 */
fun getAtomicBlockInnerLocations(builder: XcfaProcedureBuilder): List<XcfaLocation> =
  getAtomicBlockInnerLocations(builder.initLoc)

private fun getAtomicBlockInnerLocations(initialLocation: XcfaLocation): List<XcfaLocation> {
  val atomicLocations = mutableListOf<XcfaLocation>()
  val visitedLocations = mutableListOf<XcfaLocation>()
  val locationsToVisit = mutableListOf(initialLocation)
  val isAtomic = mutableMapOf(initialLocation to false)
  while (locationsToVisit.isNotEmpty()) {
    val visiting = locationsToVisit.removeAt(0)
    if (checkNotNull(isAtomic[visiting])) atomicLocations.add(visiting)
    visitedLocations.add(visiting)
    for (outEdge in visiting.outgoingEdges) {
      var isNextAtomic = checkNotNull(isAtomic[visiting])
      if (outEdge.getFlatLabels().any { it.isAtomicBegin }) {
        isNextAtomic = true
      }
      if (outEdge.getFlatLabels().any { it.isAtomicEnd }) {
        isNextAtomic = false
      }
      val target = outEdge.target
      isAtomic[target] = isNextAtomic
      if (target in atomicLocations && !isNextAtomic) {
        atomicLocations.remove(target)
      }
      if (target !in locationsToVisit && target !in visitedLocations) {
        locationsToVisit.add(outEdge.target)
      }
    }
  }
  return atomicLocations
}

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
      is MemoryAssignStmt<*, *, *> -> expr.dereferences + listOf(deref)
      else -> emptyList()
    }

val Expr<*>.dereferences: List<Dereference<*, *, *>>
  get() =
    if (this is Dereference<*, *, *>) {
      ops.flatMap { it.dereferences } + listOf(this)
    } else {
      ops.flatMap { it.dereferences }
    }

val XcfaLabel.dereferencesWithAccessTypes: List<Pair<Dereference<*, *, *>, AccessType>>
  get() =
    when (this) {
      is NondetLabel -> error("NondetLabel is not well-defined for dereferences due to ordering")
      is SequenceLabel -> labels.flatMap(XcfaLabel::dereferencesWithAccessTypes)
      is InvokeLabel -> params.flatMap { it.dereferences.map { Pair(it, READ) } }
      is StartLabel -> params.flatMap { it.dereferences.map { Pair(it, READ) } }
      is StmtLabel -> stmt.dereferencesWithAccessTypes

      else -> listOf()
    }

val Stmt.dereferencesWithAccessTypes: List<Pair<Dereference<*, *, *>, AccessType>>
  get() =
    when (this) {
      is MemoryAssignStmt<*, *, *> ->
        expr.dereferences.map { Pair(it, READ) } + listOf(Pair(deref, WRITE))
      is AssignStmt<*> -> expr.dereferences.map { Pair(it, READ) }
      is AssumeStmt -> cond.dereferences.map { Pair(it, READ) }
      else -> listOf()
    }

fun XcfaLabel.simplify(valuation: MutableValuation, parseContext: ParseContext): XcfaLabel =
  if (this is StmtLabel) {
    val simplified = stmt.accept(StmtSimplifier.StmtSimplifierVisitor(), valuation).stmt
    when (stmt) {
      is MemoryAssignStmt<*, *, *> -> {
        simplified as MemoryAssignStmt<*, *, *>
        if (parseContext.metadata.getMetadataValue(stmt.expr, "cType").isPresent)
          parseContext.metadata.create(
            simplified.expr,
            "cType",
            CComplexType.getType(stmt.expr, parseContext),
          )
        if (parseContext.metadata.getMetadataValue(stmt.deref, "cType").isPresent)
          parseContext.metadata.create(
            simplified.deref,
            "cType",
            CComplexType.getType(stmt.deref, parseContext),
          )
        StmtLabel(simplified, metadata = metadata)
      }

      is AssignStmt<*> -> {
        simplified as AssignStmt<*>
        if (parseContext.metadata.getMetadataValue(stmt.expr, "cType").isPresent)
          parseContext.metadata.create(
            simplified.expr,
            "cType",
            CComplexType.getType(stmt.expr, parseContext),
          )
        StmtLabel(simplified, metadata = metadata)
      }

      is AssumeStmt -> {
        simplified as AssumeStmt
        if (parseContext.metadata.getMetadataValue(stmt.cond, "cType").isPresent) {
          parseContext.metadata.create(
            simplified.cond,
            "cType",
            CComplexType.getType(stmt.cond, parseContext),
          )
        }
        parseContext.metadata.create(simplified, "cTruth", stmt.cond is NeqExpr<*>)
        StmtLabel(simplified, metadata = metadata, choiceType = choiceType)
      }

      else -> this
    }
  } else this

data class MallocLitExpr<T : Type>(val kType: T) : NullaryExpr<T>(), LitExpr<T> {

  override fun getType(): T = kType

  override fun eval(valuation: Valuation): LitExpr<T> = this
}

val XCFA.lazyPointsToGraph: Lazy<Map<VarDecl<*>, Set<LitExpr<*>>>>
  get() = lazy {
    val attempt =
      Try.attempt {
        fun unboxMod(e: Expr<*>): Expr<*> = if (e is ModExpr<*>) unboxMod(e.ops[0]) else e

        val bases =
          this.procedures
            .flatMap {
              it.edges.flatMap {
                it.getFlatLabels().flatMap { it.dereferences.map { unboxMod(it.array) } }
              }
            }
            .filter { it !is LitExpr<*> && it !is Dereference<*, *, *> }
            .toSet()
        checkState(bases.all { it is RefExpr<*> })

        // value assignments are either assignments, or thread start statements, or procedure invoke
        // statements
        val assignments =
          this.procedures.flatMap {
            it.edges.flatMap {
              it
                .getFlatLabels()
                .filter { it is StmtLabel && it.stmt is AssignStmt<*> }
                .map { (it as StmtLabel).stmt as AssignStmt<*> }
            }
          }
        val threadStart =
          this.procedures.flatMap {
            it.edges
              .flatMap { it.getFlatLabels().filterIsInstance<StartLabel>() }
              .flatMap {
                val calledProc = this.procedures.find { proc -> proc.name == it.name }
                calledProc?.let { proc ->
                  proc.params
                    .withIndex()
                    .filter { (_, it) -> it.second != ParamDirection.OUT }
                    .map { (i, pair) ->
                      val (param, _) = pair
                      Assign(cast(param, param.type), cast(it.params[i], param.type))
                    } +
                    proc.params
                      .withIndex()
                      .filter { (i, pair) ->
                        pair.second != ParamDirection.IN && it.params[i] is RefExpr<*>
                      }
                      .map { (i, pair) ->
                        val (param, _) = pair
                        Assign(
                          cast((it.params[i] as RefExpr<*>).decl as VarDecl<*>, param.type),
                          cast(param.ref, param.type),
                        )
                      }
                } ?: listOf()
              }
          }
        val procInvoke =
          this.procedures.flatMap {
            it.edges
              .flatMap { it.getFlatLabels().filterIsInstance<InvokeLabel>() }
              .flatMap {
                val calledProc = this.procedures.find { proc -> proc.name == it.name }
                calledProc?.let { proc ->
                  proc.params
                    .filter { it.second != ParamDirection.OUT }
                    .mapIndexed { i, (param, _) ->
                      Assign(cast(param, param.type), cast(it.params[i], param.type))
                    } +
                    proc.params
                      .filter { it.second != ParamDirection.IN }
                      .mapIndexed { i, (param, _) ->
                        Assign(
                          cast((it.params[i] as RefExpr<*>).decl as VarDecl<*>, param.type),
                          cast(param.ref, param.type),
                        )
                      }
                } ?: listOf()
              }
          }

        val allAssignments = (assignments + threadStart + procInvoke)

        val ptrVars = LinkedHashSet<VarDecl<*>>(bases.map { (it as RefExpr<*>).decl as VarDecl<*> })
        var lastPtrVars = emptySet<VarDecl<*>>()

        while (ptrVars != lastPtrVars) {
          lastPtrVars = ptrVars.toSet()

          val rhs = allAssignments.filter { ptrVars.contains(it.varDecl) }.map { unboxMod(it.expr) }
          allAssignments.filter {
            ptrVars.contains(it.varDecl) && (it.expr !is LitExpr<*>) && (it.expr !is RefExpr<*>)
          }
          ptrVars.addAll(rhs.filterIsInstance(RefExpr::class.java).map { it.decl as VarDecl<*> })
        }

        val lits = LinkedHashMap<VarDecl<*>, MutableSet<LitExpr<*>>>()
        val alias = LinkedHashMap<VarDecl<*>, MutableSet<VarDecl<*>>>()

        val litAssignments =
          allAssignments
            .filter { ptrVars.contains(it.varDecl) && unboxMod(it.expr) is LitExpr<*> }
            .map { Pair(it.varDecl, unboxMod(it.expr) as LitExpr<*>) } +
            allAssignments
              .filter {
                ptrVars.contains(it.varDecl) &&
                  (unboxMod(it.expr) !is LitExpr<*> && unboxMod(it.expr) !is RefExpr<*>)
              }
              .map { Pair(it.varDecl, MallocLitExpr(it.varDecl.type)) }
        litAssignments.forEach { lits.getOrPut(it.first) { LinkedHashSet() }.add(it.second) }
        val varAssignments =
          allAssignments
            .filter { ptrVars.contains(it.varDecl) && unboxMod(it.expr) is RefExpr<*> }
            .map { Pair(it.varDecl, (unboxMod(it.expr) as RefExpr<*>).decl as VarDecl<*>) }
        varAssignments.forEach { alias.getOrPut(it.first) { LinkedHashSet() }.add(it.second) }
        varAssignments.forEach { lits.putIfAbsent(it.first, LinkedHashSet()) }

        var lastLits = emptyMap<VarDecl<*>, MutableSet<LitExpr<*>>>()
        while (lastLits != lits) {
          lastLits = lits.toMap()
          alias.forEach {
            lits
              .getOrPut(it.key) { LinkedHashSet() }
              .addAll(it.value.flatMap { lits.getOrDefault(it, emptySet()) })
          }
        }

        lits.filter { bases.contains(it.key.ref) }
      }
    if (attempt.isSuccess) {
      attempt.asSuccess().value
    } else {
      emptyMap()
    }
  }

fun Collection<VarDecl<*>>.pointsTo(xcfa: XCFA) =
  flatMap { xcfa.pointsToGraph[it] ?: emptyList() }.toSet()

fun VarAccessMap.pointsTo(xcfa: XCFA) = keys.pointsTo(xcfa)

private fun <T : Type> assignStmtLabelOf(
  lhs: VarDecl<T>,
  rhs: Expr<T>,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = StmtLabel(Assign(lhs, rhs), metadata = metadata)

@Suppress("FunctionName")
fun <T1 : Type, T2 : Type> AssignStmtLabel(
  lhs: VarDecl<T1>,
  rhs: Expr<T2>,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = assignStmtLabelOf(lhs, cast(rhs, lhs.type), metadata)

@Suppress("FunctionName")
fun <T1 : Type, T2 : Type, T3 : Type> AssignStmtLabel(
  lhs: VarDecl<T1>,
  rhs: Expr<T2>,
  type: T3,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = assignStmtLabelOf(cast(lhs, type), cast(rhs, type), metadata)

@Suppress("FunctionName")
fun <T1 : Type, T2 : Type> AssignStmtLabel(
  lhs: RefExpr<T1>,
  rhs: Expr<T2>,
  metadata: MetaData = EmptyMetaData,
): StmtLabel = assignStmtLabelOf(cast(lhs.decl as VarDecl<*>, rhs.type), rhs, metadata)
