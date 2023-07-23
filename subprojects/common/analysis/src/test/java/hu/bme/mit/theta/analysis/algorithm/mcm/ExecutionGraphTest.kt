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
package hu.bme.mit.theta.analysis.algorithm.mcm

import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.ExecutionGraph
import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.TVL
import hu.bme.mit.theta.analysis.algorithm.mcm.mcm.MCM
import hu.bme.mit.theta.analysis.algorithm.mcm.mcm.MCMConstraint
import hu.bme.mit.theta.analysis.algorithm.mcm.mcm.MCMRelation
import hu.bme.mit.theta.common.TupleN
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import org.junit.Assert
import org.junit.Test

class ExecutionGraphTest {

    @Test
    fun test() {
        val mcm: MCM = MCM("test-mcm")
        mcm.addConstraint(
            MCMConstraint(
                MCMRelation(2, "po"),
                MCMConstraint.ConstraintType.ACYCLIC
            ))
        val solver = Z3SolverFactory.getInstance().createSolver()

        val executionGraph = ExecutionGraph()
        executionGraph.addEvent(0)
        executionGraph.addEvent(1)
        executionGraph.addEvent(2)

        executionGraph["po", TupleN.of(0, 1)] = TVL.TRUE
        executionGraph["po", TupleN.of(0, 2)] = TVL.TRUE
        executionGraph["po", TupleN.of(1, 2)] = TVL.TRUE

        solver.push()
        solver.add(executionGraph.toExpr(mcm))
        val safeResult = solver.check()
        Assert.assertTrue(safeResult.isSat)
        solver.pop()

        executionGraph["po", TupleN.of(2, 0)] = TVL.TRUE

        solver.push()
        solver.add(executionGraph.toExpr(mcm))
        val unsafeResult = solver.check()
        Assert.assertTrue(unsafeResult.isUnsat)
        solver.pop()
    }
}