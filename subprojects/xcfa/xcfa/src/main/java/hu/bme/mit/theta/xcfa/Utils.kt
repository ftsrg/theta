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

package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.model.*
import java.util.function.Predicate


/**
 * Get flattened label list (without sequence labels).
 */
fun XcfaEdge.getFlatLabels(): List<XcfaLabel> = label.getFlatLabels()

fun XcfaLabel.getFlatLabels(): List<XcfaLabel> = when (this) {
    is SequenceLabel -> {
        val ret = mutableListOf<XcfaLabel>()
        labels.forEach { ret.addAll(it.getFlatLabels()) }
        ret
    }

    else -> listOf(this)
}

fun XCFA.collectVars(): Iterable<VarDecl<*>> = vars.map { it.wrappedVar } union procedures.map { it.vars }.flatten()

fun XCFA.collectAssumes(): Iterable<Expr<BoolType>> = procedures.map { procedure ->
    procedure.edges.map { it.label.collectAssumes() }.flatten()
}.flatten()

fun XcfaLabel.collectAssumes(): Iterable<Expr<BoolType>> = when (this) {
    is StmtLabel -> when (stmt) {
        is AssumeStmt -> setOf(stmt.cond)
        else -> setOf()
    }

    is NondetLabel -> labels.map { it.collectAssumes() }.flatten()
    is SequenceLabel -> labels.map { it.collectAssumes() }.flatten()
    else -> setOf()
}

fun XcfaLabel.collectAssumesVars(): Set<VarDecl<*>> {
    return collectAssumes().flatMap {
        val v = mutableSetOf<VarDecl<*>>()
        ExprUtils.collectVars(it, v)
        v
    }.toSet()
}

fun XcfaLabel.collectHavocs(): Set<HavocStmt<*>> = when (this) {
    is StmtLabel -> when (stmt) {
        is HavocStmt<*> -> setOf(stmt)
        else -> setOf()
    }

    is NondetLabel -> labels.map { it.collectHavocs() }.flatten().toSet()
    is SequenceLabel -> labels.map { it.collectHavocs() }.flatten().toSet()
    else -> setOf()
}

fun XcfaLabel.collectVars(): Iterable<VarDecl<*>> = when (this) {
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
private typealias VarAccessMap = Map<VarDecl<*>, AccessType>

val AccessType?.isRead get() = this?.first == true
val AccessType?.isWritten get() = this?.second == true
fun AccessType?.merge(other: AccessType?) =
    Pair(this?.first == true || other?.first == true, this?.second == true || other?.second == true)

val WRITE: AccessType get() = Pair(false, true)
val READ: AccessType get() = Pair(true, false)

private fun List<VarAccessMap>.mergeAndCollect(): VarAccessMap = this.fold(mapOf()) { acc, next ->
    (acc.keys + next.keys).associateWith { acc[it].merge(next[it]) }
}

private operator fun VarAccessMap?.plus(other: VarAccessMap?): VarAccessMap =
    listOfNotNull(this, other).mergeAndCollect()

/**
 * The list of mutexes acquired by the label.
 */
inline val FenceLabel.acquiredMutexes: Set<String>
    get() = labels.mapNotNull {
        when {
            it == "ATOMIC_BEGIN" -> "___atomic_block_mutex___"
            it.startsWith("mutex_lock") -> it.substringAfter('(').substringBefore(')')
            it.startsWith("cond_wait") -> it.substring("cond_wait".length + 1, it.length - 1).split(",")[1]
            else -> null
        }
    }.toSet()

/**
 * The list of mutexes released by the label.
 */
inline val FenceLabel.releasedMutexes: Set<String>
    get() = labels.mapNotNull {
        when {
            it == "ATOMIC_END" -> "___atomic_block_mutex___"
            it.startsWith("mutex_unlock") -> it.substringAfter('(').substringBefore(')')
            it.startsWith("start_cond_wait") -> it.substring("start_cond_wait".length + 1, it.length - 1).split(",")[1]
            else -> null
        }
    }.toSet()

/**
 * Returns the list of accessed variables by the edge associated with an AccessType object.
 */
fun XcfaEdge.collectVarsWithAccessType(): VarAccessMap = label.collectVarsWithAccessType()

/**
 * Returns the list of accessed variables by the label.
 * The variable is associated with an AccessType object based on whether the variable is read/written by the label.
 */
fun XcfaLabel.collectVarsWithAccessType(): VarAccessMap = when (this) {
    is StmtLabel -> {
        when (stmt) {
            is HavocStmt<*> -> mapOf(stmt.varDecl to WRITE)
            is AssignStmt<*> -> ExprUtils.getVars(stmt.expr).associateWith { READ } + mapOf(stmt.varDecl to WRITE)
            else -> StmtUtils.getVars(stmt).associateWith { READ }
        }
    }

    is NondetLabel -> labels.map { it.collectVarsWithAccessType() }.mergeAndCollect()
    is SequenceLabel -> labels.map { it.collectVarsWithAccessType() }.mergeAndCollect()
    is InvokeLabel -> params.map { ExprUtils.getVars(it) }.flatten().associateWith { READ }
    is StartLabel -> params.map { ExprUtils.getVars(it) }.flatten().associateWith { READ } + mapOf(pidVar to READ)
    is JoinLabel -> mapOf(pidVar to READ)
    is ReadLabel -> mapOf(global to READ, local to READ)
    is WriteLabel -> mapOf(global to WRITE, local to WRITE)
    else -> emptyMap()
}

/**
 * Returns the global variables accessed by the label (the variables present in the given argument).
 */
private fun XcfaLabel.collectGlobalVars(globalVars: Set<VarDecl<*>>): VarAccessMap =
    collectVarsWithAccessType().filter { labelVar -> globalVars.any { it == labelVar.key } }

/**
 * Returns the global variables (potentially indirectly) accessed by the edge.
 * If the edge starts an atomic block, all variable accesses in the atomic block are returned.
 * Variables are associated with a pair of boolean values: the first is true if the variable is read and false otherwise. The second is similar for write access.
 */
fun XcfaEdge.collectIndirectGlobalVarAccesses(xcfa: XCFA): VarAccessMap {
    val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar).toSet()
    val flatLabels = getFlatLabels()
    val mutexes = flatLabels.filterIsInstance<FenceLabel>().flatMap { it.acquiredMutexes }.toMutableSet()
    return if (mutexes.isEmpty()) {
        label.collectGlobalVars(globalVars)
    } else {
        collectGlobalVarsWithTraversal(globalVars) { it.mutexOperations(mutexes) }
    }
}

/**
 * Represents a global variable access: stores the variable declaration, the access type (read/write) and the set of
 * mutexes that are needed to perform the variable access.
 */
class GlobalVarAccessWithMutexes(val varDecl: VarDecl<*>, val access: AccessType, val mutexes: Set<String>)

/**
 * Returns the global variable accesses of the edge.
 *
 * @param xcfa the XCFA that contains the edge
 * @param currentMutexes the set of mutexes currently acquired by the process of the edge
 * @return the list of global variable accesses (c.f., [GlobalVarAccessWithMutexes])
 */
fun XcfaEdge.getGlobalVarsWithNeededMutexes(xcfa: XCFA, currentMutexes: Set<String>): List<GlobalVarAccessWithMutexes> {
    val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar).toSet()
    val neededMutexes = currentMutexes.toMutableSet()
    val accesses = mutableListOf<GlobalVarAccessWithMutexes>()
    getFlatLabels().forEach { label ->
        if (label is FenceLabel) {
            neededMutexes.addAll(label.acquiredMutexes)
        } else {
            val vars = label.collectGlobalVars(globalVars)
            accesses.addAll(vars.mapNotNull { (varDecl, accessType) ->
                if (accesses.any { it.varDecl == varDecl && (it.access == accessType && it.access == WRITE) }) {
                    null
                } else {
                    GlobalVarAccessWithMutexes(varDecl, accessType, neededMutexes.toSet())
                }
            })
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
private fun XcfaEdge.collectGlobalVarsWithTraversal(globalVars: Set<VarDecl<*>>, goFurther: Predicate<XcfaEdge>)
    : VarAccessMap {
    val vars = mutableMapOf<VarDecl<*>, AccessType>()
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
 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an AtomicBegin and before
 * an edge with an AtomicEnd).
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
            if (outEdge.getFlatLabels().any { it is FenceLabel && it.labels.contains("ATOMIC_BEGIN") }) {
                isNextAtomic = true
            }
            if (outEdge.getFlatLabels().any { it is FenceLabel && it.labels.contains("ATOMIC_END") }) {
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