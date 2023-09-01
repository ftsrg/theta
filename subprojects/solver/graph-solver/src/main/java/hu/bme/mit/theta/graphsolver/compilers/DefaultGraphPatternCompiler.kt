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

abstract class DefaultGraphPatternCompiler<T> : GraphPatternCompiler<T?, T?> {

    override fun addEvents(events: List<Int>) {}
    override fun addFacts(edges: Map<Pair<String, Tuple>, ThreeVL>) {}
    override fun compile(acyclic: Acyclic): T? = acyclic.constrainedRule.accept(this)
    override fun compile(cyclic: Cyclic): T? = cyclic.constrainedRule.accept(this)
    override fun compile(empty: Empty): T? = empty.constrainedRule.accept(this)
    override fun compile(nonempty: Nonempty): T? = nonempty.constrainedRule.accept(this)
    override fun compile(reflexive: Reflexive): T? = reflexive.constrainedRule.accept(this)
    override fun compile(irreflexive: Irreflexive): T? = irreflexive.constrainedRule.accept(this)

    override fun compile(pattern: CartesianProduct): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: Complement): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: ComplementNode): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: Difference): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: DifferenceNode): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: Domain): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: EmptySet): T? = null
    override fun compile(pattern: EmptyRel): T? = null
    override fun compile(pattern: IdentityClosure): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: Intersection): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: IntersectionNode): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: Inverse): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: Range): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: ReflexiveTransitiveClosure): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: Self): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: Sequence): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: Toid): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: TransitiveClosure): T? {
        pattern.op.accept(this); return null
    }

    override fun compile(pattern: Union): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: UnionNode): T? {
        pattern.op1.accept(this); pattern.op2.accept(this); return null
    }

    override fun compile(pattern: BasicEventSet): T? = null
    override fun compile(pattern: BasicRelation): T? = null

    override fun getCompleteGraph(mcm: Set<GraphPattern>,
        model: Valuation): Pair<List<Int>, Map<Pair<String, Tuple>, ThreeVL>> {
        error("Not implemented")
    }
}