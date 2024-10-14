/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.core.model.Valuation

class ConcreteSummaryBuilder<A: Action> {
    fun <S: State> build(
        valuations: MutableMap<SummaryNode<S, A>, Valuation>,
        summary: AbstractTraceSummary<S, A>
    ): ConcreteSummary<Valuation, A> {
        // TODO check that every node has a valuation?
        // TODO make valuation into a template type?

        // create nodes (states/valuations)
        val concreteNodeMap: MutableMap<SummaryNode<S, A>, ConcreteSummaryNode<Valuation, A>> = mutableMapOf()
        for(node in summary.summaryNodes) {
            concreteNodeMap[node] = ConcreteSummaryNode<Valuation, A>(valuations[node]!!)
        }

        // create edges (actions)
        val edges: MutableSet<ConcreteSummaryEdge<Valuation, A>> = mutableSetOf()
        for((summaryNode, concreteNode) in concreteNodeMap) {
            for(summaryEdge in summaryNode.outEdges) {
                edges.add(ConcreteSummaryEdge.create(summaryEdge.action, concreteNode, concreteNodeMap[summaryEdge.target]!!))
            }
        }

        // create concrete summary
        return ConcreteSummary(concreteNodeMap.values.toSet(), edges)
    }
}

data class ConcreteSummary<S, A>(val nodes: Set<ConcreteSummaryNode<S, A>>, val edges: Set<ConcreteSummaryEdge<S, A>>)

class ConcreteSummaryNode<S, A>(val state: S) {
    val inEdges : MutableSet<ConcreteSummaryEdge<S,A>> = mutableSetOf()
    val outEdges : MutableSet<ConcreteSummaryEdge<S,A>> = mutableSetOf()
    
    fun addInEdge(edge: ConcreteSummaryEdge<S, A>) {
        inEdges.add(edge)
    }

    fun addOutEdge(edge: ConcreteSummaryEdge<S, A>) {
        outEdges.add(edge)
    }
}

class ConcreteSummaryEdge<S, A> private constructor(val action : A, val source: ConcreteSummaryNode<S, A>, val target: ConcreteSummaryNode<S, A>) {
    companion object {
        fun <S, A> create(action: A, source: ConcreteSummaryNode<S, A>, target: ConcreteSummaryNode<S, A>) : ConcreteSummaryEdge<S, A> {
            val edge = ConcreteSummaryEdge<S, A>(action, source, target)
            source.addOutEdge(edge)
            target.addInEdge(edge)
            return edge
        }
    }
}