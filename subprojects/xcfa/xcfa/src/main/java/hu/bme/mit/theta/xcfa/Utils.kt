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
import hu.bme.mit.theta.core.stmt.AssumeStmt
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

fun XCFA.getSymbols(): Pair<XcfaScope, Env> {
    val symbolTable = SymbolTable()
    val scope = XcfaScope(symbolTable)
    val vars = collectVars()
    val env = Env()
    vars.forEach {
        val symbol = Symbol { it.name.lowercase() }
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