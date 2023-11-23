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
package hu.bme.mit.theta.xcfa.analysis.pointers

import hu.bme.mit.theta.common.disjointset.DisjointSet
import hu.bme.mit.theta.core.utils.PointerStore
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.model.XCFA
import kotlin.math.absoluteValue

class DisjointSetMember(val varDecl: VarDecl<*>, val derefLevel: Int) {
    override fun toString(): String {
        val prefixChar = if (derefLevel < 0) "&" else "*"
        return prefixChar.repeat(derefLevel.absoluteValue) + varDecl.name
    }

    override fun equals(other: Any?): Boolean {
        if (other !is DisjointSetMember) {
            return false
        }
        return (varDecl.name == other.varDecl.name) && (derefLevel == other.derefLevel)
    }

    override fun hashCode(): Int {
        var result = varDecl.name.hashCode()
        result = 31 * result + derefLevel
        return result
    }
}

class SteensgaardsPointerAnalysis : PointerAnalysis() {

    private val disjointSet = DisjointSet<DisjointSetMember>()
    private val disjointSetEdges = mutableSetOf<Pair<DisjointSetMember, DisjointSetMember>>()
    private val pointerStore = PointerStore()

    private fun join(x: DisjointSetMember, y: DisjointSetMember) {
        if (x == y) {
            return
        }
        val xStar = DisjointSetMember(x.varDecl, x.derefLevel + 1)
        val yStar = DisjointSetMember(y.varDecl, y.derefLevel + 1)
        disjointSet.union(x, y)
        if (disjointSet.has(xStar) && disjointSet.has(yStar)) {
            join(xStar, yStar)
        }
    }

    private fun addVarToDisjointSet(x: DisjointSetMember) {
        val xAmp = DisjointSetMember(x.varDecl, x.derefLevel - 1)
        val xStar = DisjointSetMember(x.varDecl, x.derefLevel + 1)
        disjointSet.makeSet(x)
        disjointSet.makeSet(xAmp)
        disjointSet.makeSet(xStar)
        disjointSetEdges.add(xAmp to x)
        disjointSetEdges.add(x to xStar)
    }

    override fun run(xcfa: XCFA): PointerStore {
        val actions = getPointerActions(xcfa)
        return runOnActions(actions)
    }

    override fun runOnActions(actions: List<PointerAction>): PointerStore {
        actions.forEach { action ->
            val pVarDecl = action.p
            val qVarDecl = action.q
            when (action) {
                is ReferencingPointerAction -> {
                    // p = &q
                    val pStar = DisjointSetMember(pVarDecl, 1)
                    val q = DisjointSetMember(qVarDecl, 0)

                    addVarToDisjointSet(pStar)
                    addVarToDisjointSet(q)

                    join(pStar, q)
                }
                is DereferencingWritePointerAction -> {
                    // *p = q
                    val pStarStar = DisjointSetMember(pVarDecl, 2)
                    val qStar = DisjointSetMember(qVarDecl, 1)

                    addVarToDisjointSet(pStarStar)
                    addVarToDisjointSet(qStar)

                    join(pStarStar, qStar)
                }
                is DereferencingReadPointerAction -> {
                    // p = *q
                    val pStar = DisjointSetMember(pVarDecl, 1)
                    val qStarStar = DisjointSetMember(qVarDecl, 2)

                    addVarToDisjointSet(pStar)
                    addVarToDisjointSet(qStarStar)

                    join(pStar, qStarStar)
                }
                is AliasingPointerAction -> {
                    // p = q
                    val pStar = DisjointSetMember(pVarDecl, 1)
                    val qStar = DisjointSetMember(qVarDecl, 1)

                    addVarToDisjointSet(pStar)
                    addVarToDisjointSet(qStar)

                    join(pStar, qStar)
                }
            }
        }

        fillPointerStoreFromDisjointSet()
        return pointerStore
    }

    private fun fillPointerStoreFromDisjointSet() {
        val sets = disjointSet.getSets()
        sets.forEach { set ->
            val members = set.value
            members.forEach { member ->
                if (member.derefLevel == 0) {
                    pointerStore.addPointer(member.varDecl)
                }
            }
        }
        disjointSetEdges.forEach { (source, target) ->
            val sourceRoot = disjointSet.find(source)
            val targetRoot = disjointSet.find(target)
            val sourceMembers = sets[sourceRoot]!!
            val targetMembers = sets[targetRoot]!!
            sourceMembers.forEach { sourceMember ->
                targetMembers.forEach { targetMember ->
                    if (sourceMember.derefLevel == 0 && targetMember.derefLevel == 0 && sourceMember != targetMember && sourceRoot != targetRoot) {
                        pointerStore.addPointsTo(sourceMember.varDecl, targetMember.varDecl)
                    }
                }
            }
        }
    }
}