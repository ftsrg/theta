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

package hu.bme.mit.theta.graphsolver

import hu.bme.mit.theta.graphsolver.patterns.constraints.*
import hu.bme.mit.theta.graphsolver.patterns.patterns.*

fun GraphConstraint.collectSubRelations(): Set<GraphPattern> = when (this) {
    is Acyclic -> this.constrainedRule.collectSubRelations()
    is Cyclic -> this.constrainedRule.collectSubRelations()
    is Empty -> this.constrainedRule.collectSubRelations()
    is Irreflexive -> this.constrainedRule.collectSubRelations()
    is Nonempty -> this.constrainedRule.collectSubRelations()
    is Reflexive -> this.constrainedRule.collectSubRelations()
}

fun GraphPattern.collectSubRelations(): Set<GraphPattern> = when (this) {
    is BasicRelation -> emptySet()
    is CartesianProduct -> op1.collectSubRelations() union op2.collectSubRelations()
    is Complement -> op.collectSubRelations()
    is Difference -> op1.collectSubRelations() union op2.collectSubRelations()
    EmptyRel -> emptySet()
    EmptySet -> emptySet()
    is IdentityClosure -> op.collectSubRelations()
    is Intersection -> op1.collectSubRelations() union op2.collectSubRelations()
    is Inverse -> op.collectSubRelations()
    is ReflexiveTransitiveClosure -> op.collectSubRelations()
    is Self -> op.collectSubRelations()
    is Sequence -> op1.collectSubRelations() union op2.collectSubRelations()
    is Toid -> op.collectSubRelations()
    is TransitiveClosure -> op.collectSubRelations()
    is Union -> op1.collectSubRelations() union op2.collectSubRelations()
    is BasicEventSet -> emptySet()
    is ComplementNode -> op.collectSubRelations()
    is DifferenceNode -> op1.collectSubRelations() union op2.collectSubRelations()
    is Domain -> op.collectSubRelations()
    is IntersectionNode -> op1.collectSubRelations() union op2.collectSubRelations()
    is Range -> op.collectSubRelations()
    is UnionNode -> op1.collectSubRelations() union op2.collectSubRelations()
    else -> error("Should not be here")
} union if (patternName != null) setOf(this) else emptySet()