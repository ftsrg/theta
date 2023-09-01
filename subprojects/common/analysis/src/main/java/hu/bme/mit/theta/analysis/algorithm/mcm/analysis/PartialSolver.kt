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

package hu.bme.mit.theta.analysis.algorithm.mcm.analysis

import hu.bme.mit.theta.common.Tuple
import hu.bme.mit.theta.graphsolver.ThreeVL
import hu.bme.mit.theta.graphsolver.collectSubRelations
import hu.bme.mit.theta.graphsolver.compilers.GraphPatternCompiler
import hu.bme.mit.theta.graphsolver.patterns.constraints.GraphConstraint
import hu.bme.mit.theta.graphsolver.solvers.GraphSolver

class PartialSolver<T>(
    private val mcm: Collection<GraphConstraint>,
    private val partialGraph: CandidateExecutionGraph,
    private val graphPatternCompiler: GraphPatternCompiler<T, *>,
    private val graphPatternSolver: GraphSolver<T>
) {

    fun getSolution(): CandidateExecutionGraph? {
        graphPatternCompiler.addEvents(partialGraph.nodes)
        graphPatternCompiler.addFacts(partialGraph.knownEvents)

        val exprs = mcm.map { it.accept(graphPatternCompiler) }
        exprs.forEach { graphPatternSolver.add(it) }

        val namedPatterns = mcm.map { it.collectSubRelations() }.flatten().toSet()

        val status = graphPatternSolver.check()

        return if (status.isSat) {
            val (nodes, events) = graphPatternCompiler.getCompleteGraph(namedPatterns, graphPatternSolver.getModel())
            CandidateExecutionGraph(nodes, events)
        } else null
    }

}

data class CandidateExecutionGraph(
    val nodes: List<Int>,
    val knownEvents: Map<Pair<String, Tuple>, ThreeVL>) {
}