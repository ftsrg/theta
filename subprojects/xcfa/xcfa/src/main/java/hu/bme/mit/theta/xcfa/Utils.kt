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

package hu.bme.mit.theta.xcfa

import com.google.common.collect.Sets
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


fun XCFA.collectVars(): Iterable<VarDecl<*>> = vars.map { it.wrappedVar }.union(procedures.map { it.vars }.flatten())

fun XCFA.collectAssumes(): Iterable<Expr<BoolType>> = procedures.map { it.edges.map { it.label.collectAssumes() }.flatten() }.flatten()
fun XcfaLabel.collectAssumes(): Iterable<Expr<BoolType>> = when(this) {
    is StmtLabel -> when(stmt) {
        is AssumeStmt -> setOf(stmt.cond)
        else -> setOf()
    }
    is NondetLabel -> labels.map { it.collectAssumes() }.flatten()
    is SequenceLabel -> labels.map { it.collectAssumes() }.flatten()
    else -> setOf()
}
fun XcfaLabel.collectVars(): Iterable<VarDecl<*>> = when(this) {
    is StmtLabel -> StmtUtils.getVars(stmt)
    is NondetLabel -> labels.map { it.collectVars() }.flatten()
    is SequenceLabel -> labels.map { it.collectVars() }.flatten()
    is InvokeLabel -> params.map { ExprUtils.getVars(it) }.flatten()
    is JoinLabel -> setOf(pidVar)
    is ReadLabel -> setOf(global, local)
    is StartLabel ->  Sets.union(params.map { ExprUtils.getVars(it) }.flatten().toSet(), setOf(pidVar))
    is WriteLabel -> setOf(global, local)
    else -> emptySet()
}


typealias AccessType = Pair<Boolean, Boolean>
val AccessType?.isRead get() = this?.first == true
val AccessType?.isWritten get() = this?.second == true
fun AccessType?.merge(other: AccessType?) =
    Pair(this?.first == true || other?.first == true, this?.second == true || other?.second == true)
val WRITE: AccessType get() = Pair(false, true)
val READ: AccessType get() = Pair(true, false)

private typealias VarAccessMap = Map<VarDecl<*>, AccessType>
private fun List<VarAccessMap>.mergeAndCollect(): VarAccessMap = this.fold(mapOf()) { acc, next ->
    (acc.keys + next.keys).associateWith { acc[it].merge(next[it]) }
}

private fun extendRelevantVars(relevantVars: Set<VarDecl<*>>?, labels: Collection<XcfaLabel>): Set<VarDecl<*>>? =
    relevantVars?.toMutableSet()?.apply {
        val accesses = labels.map { it.collectVarsWithAccessType(null) }.mergeAndCollect()
        addAll(accesses.filter { it.value.isWritten && it.value.isRead }.keys)
    }

/**
 * Returns the list of accessed variables by the label.
 * The variable is associated with true if the variable is written and false otherwise.
 */
private fun XcfaLabel.collectVarsWithAccessType(relevantVars: Set<VarDecl<*>>?): VarAccessMap = when(this) {
    is StmtLabel -> {
        when(stmt) {
            is HavocStmt<*> -> if(relevantVars?.let { stmt.varDecl in it} != false) mapOf(stmt.varDecl to WRITE) else mapOf()
            is AssignStmt<*> -> if(relevantVars?.let { stmt.varDecl in it} != false)
                                    StmtUtils.getVars(stmt).associateWith { READ } + mapOf(stmt.varDecl to WRITE)
                                else
                                    mapOf()
            else -> StmtUtils.getVars(stmt).associateWith { READ }
        }
    }
    is NondetLabel -> {
        labels.map { it.collectVarsWithAccessType(extendRelevantVars(relevantVars, labels)) }.mergeAndCollect()
    }
    is SequenceLabel -> {
        labels.map { it.collectVarsWithAccessType(extendRelevantVars(relevantVars, labels)) }.mergeAndCollect()
    }
    is InvokeLabel -> params.map { ExprUtils.getVars(it) }.flatten().associateWith { READ }
    is JoinLabel -> mapOf(pidVar to READ)
    is ReadLabel -> mapOf(global to READ, local to READ)
    is StartLabel -> params.map { ExprUtils.getVars(it) }.flatten().associateWith { READ } + mapOf(pidVar to READ)
    is WriteLabel -> mapOf(global to WRITE, local to WRITE)
    else -> emptyMap()
}

/**
 * Returns the global variables accessed by the label (the variables present in the given argument).
 */
private fun XcfaLabel.collectGlobalVars(globalVars: Set<VarDecl<*>>, relevantVars: Set<VarDecl<*>>?) =
    collectVarsWithAccessType(relevantVars).filter { labelVar -> globalVars.any { it == labelVar.key } }

inline val XcfaLabel.isAtomicBegin get() = this is FenceLabel && this.labels.contains("ATOMIC_BEGIN")
inline val XcfaLabel.isAtomicEnd get() = this is FenceLabel && this.labels.contains("ATOMIC_END")

/**
 * Returns the global variables (potentially indirectly) accessed by the edge.
 * If the edge starts an atomic block, all variable accesses in the atomic block is returned.
 * Variables are associated with a boolean value: true if the variable is written and false otherwise.
 */
fun XcfaEdge.getGlobalVars(xcfa: XCFA, relevantVars: Set<VarDecl<*>>? = null): Map<VarDecl<*>, AccessType> {
    val globalVars = xcfa.vars.map(XcfaGlobalVar::wrappedVar).toSet()
    var label = this.label
    if (label is SequenceLabel && label.labels.size == 1) label = label.labels[0]
    if (label.isAtomicBegin || (label is SequenceLabel && label.labels.any { it.isAtomicBegin } && label.labels.none { it.isAtomicEnd })) {
        val vars = mutableMapOf<VarDecl<*>, AccessType>()
        val processed = mutableSetOf<XcfaEdge>()
        val unprocessed = mutableListOf(this)
        while (unprocessed.isNotEmpty()) {
            val e = unprocessed.removeFirst()
            var eLabel = e.label
            if (eLabel is SequenceLabel && eLabel.labels.size == 1) eLabel = eLabel.labels[0]
            eLabel.collectGlobalVars(globalVars, relevantVars).forEach { (varDecl, accessType) ->
                vars[varDecl] = accessType.merge(vars[varDecl])
            }
            processed.add(e)
            if (!(eLabel.isAtomicEnd || (eLabel is SequenceLabel && eLabel.labels.any { it.isAtomicEnd }))) {
                unprocessed.addAll(e.target.outgoingEdges subtract processed)
            }
        }
        return vars
    } else {
        return label.collectGlobalVars(globalVars, relevantVars)
    }
}

/**
 * Returns true if the edge starts an atomic block.
 */
fun XcfaEdge.startsAtomic(): Boolean {
    var label = this.label
    if (label is SequenceLabel && label.labels.size == 1) label = label.labels[0]
    return label is FenceLabel && label.labels.contains("ATOMIC_BEGIN")
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

private val atomicBlockInnerLocationsCache: HashMap<XcfaProcedure, List<XcfaLocation>> = HashMap()

/**
 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an AtomicBegin and before
 * an edge with an AtomicEnd).
 *
 * @param xcfaProcedure the atomic block inner locations of this XCFA procedure will be returned
 * @return the list of locations in an atomic block
 */
fun getAtomicBlockInnerLocations(xcfaProcedure: XcfaProcedure): List<XcfaLocation>? {
    if (atomicBlockInnerLocationsCache.containsKey(xcfaProcedure)) {
        return atomicBlockInnerLocationsCache[xcfaProcedure]
    }
    val atomicBlockInnerLocations: List<XcfaLocation> = getAtomicBlockInnerLocations(xcfaProcedure.initLoc)
    atomicBlockInnerLocationsCache[xcfaProcedure] = atomicBlockInnerLocations
    return atomicBlockInnerLocations
}

/**
 * Returns XCFA locations that are inner locations of any atomic block (after an edge with an AtomicBegin and before
 * an edge with an AtomicEnd).
 *
 * @param builder the atomic block inner locations of the procedure of this builder will be returned
 * @return the list of locations in an atomic block
 */
fun getAtomicBlockInnerLocations(builder: XcfaProcedureBuilder): List<XcfaLocation> {
    return getAtomicBlockInnerLocations(builder.initLoc)
}

/**
 * Get flattened label list (without sequence labels).
 * Fails if a nondet label is encountered.
 */
fun XcfaEdge.getFlatLabels(): List<XcfaLabel> = label.getFlatLabels()

fun XcfaLabel.getFlatLabels(): List<XcfaLabel> = when(this) {
    is SequenceLabel -> {
        val ret = ArrayList<XcfaLabel>()
        labels.forEach { ret.addAll(it.getFlatLabels()) }
        ret
    }
    is NondetLabel -> error("Nondet labels are not supported by flattening")
    else -> listOf(this)
}


private fun getAtomicBlockInnerLocations(initialLocation: XcfaLocation): List<XcfaLocation> {
    val atomicLocations: MutableList<XcfaLocation> = ArrayList()
    val visitedLocations: MutableList<XcfaLocation> = ArrayList()
    val locationsToVisit: MutableList<XcfaLocation> = ArrayList()
    val isAtomic: HashMap<XcfaLocation, Boolean> = HashMap()
    locationsToVisit.add(initialLocation)
    isAtomic[initialLocation] = false
    while (!locationsToVisit.isEmpty()) {
        val visiting = locationsToVisit.removeAt(0)
        if (isAtomic[visiting]!!) atomicLocations.add(visiting)
        visitedLocations.add(visiting)
        for (outEdge in visiting.outgoingEdges) {
            var isNextAtomic = isAtomic[visiting]!!
            if (outEdge.getFlatLabels().stream().anyMatch { label -> label is FenceLabel && label.labels.contains("ATOMIC_BEGIN") }) {
                isNextAtomic = true
            }
            if (outEdge.getFlatLabels().stream().anyMatch { label -> label is FenceLabel && label.labels.contains("ATOMIC_END") }) {
                isNextAtomic = false
            }
            val target = outEdge.target
            isAtomic[target] = isNextAtomic
            if (atomicLocations.contains(target) && !isNextAtomic) {
                atomicLocations.remove(target)
            }
            if (!locationsToVisit.contains(target) && !visitedLocations.contains(target)) {
                locationsToVisit.add(outEdge.target)
            }
        }
    }
    return atomicLocations
}