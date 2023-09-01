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

package hu.bme.mit.theta.graphsolver.compilers

import hu.bme.mit.theta.common.Tuple
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.graphsolver.ThreeVL
import hu.bme.mit.theta.graphsolver.patterns.constraints.*
import hu.bme.mit.theta.graphsolver.patterns.patterns.*

/**
 * @param T1 Compiled constraint type
 * @param T2 Compiled pattern type
 */
interface GraphPatternCompiler<T1, T2> {

    fun addEvents(events: List<Int>)
    fun addFacts(edges: Map<Pair<String, Tuple>, ThreeVL>)
    fun compile(acyclic: Acyclic): T1
    fun compile(cyclic: Cyclic): T1
    fun compile(empty: Empty): T1
    fun compile(nonempty: Nonempty): T1
    fun compile(reflexive: Reflexive): T1
    fun compile(irreflexive: Irreflexive): T1

    fun compile(pattern: CartesianProduct): T2
    fun compile(pattern: Complement): T2
    fun compile(pattern: ComplementNode): T2
    fun compile(pattern: Difference): T2
    fun compile(pattern: DifferenceNode): T2
    fun compile(pattern: Domain): T2
    fun compile(pattern: EmptySet): T2
    fun compile(pattern: EmptyRel): T2
    fun compile(pattern: IdentityClosure): T2
    fun compile(pattern: Intersection): T2
    fun compile(pattern: IntersectionNode): T2
    fun compile(pattern: Inverse): T2
    fun compile(pattern: Range): T2
    fun compile(pattern: ReflexiveTransitiveClosure): T2
    fun compile(pattern: Self): T2
    fun compile(pattern: Sequence): T2
    fun compile(pattern: Toid): T2
    fun compile(pattern: TransitiveClosure): T2
    fun compile(pattern: Union): T2
    fun compile(pattern: UnionNode): T2
    fun compile(pattern: BasicEventSet): T2
    fun compile(pattern: BasicRelation): T2
    fun getCompleteGraph(namedPatterns: Set<GraphPattern>,
        model: Valuation): Pair<List<Int>, Map<Pair<String, Tuple>, ThreeVL>>
}