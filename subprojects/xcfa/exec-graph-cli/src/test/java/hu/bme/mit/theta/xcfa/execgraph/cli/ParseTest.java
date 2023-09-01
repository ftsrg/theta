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
package hu.bme.mit.theta.xcfa.execgraph.cli;

import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.CandidateExecutionGraph;
import hu.bme.mit.theta.analysis.algorithm.mcm.analysis.PartialSolver;
import hu.bme.mit.theta.cat.dsl.CatDslManager;
import hu.bme.mit.theta.graphsolver.compilers.pattern2expr.Pattern2ExprCompiler;
import hu.bme.mit.theta.graphsolver.patterns.constraints.GraphConstraint;
import hu.bme.mit.theta.graphsolver.solvers.SATGraphSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public class ParseTest {
    @Parameterized.Parameter(0)
    public String modelPath;

    @Parameterized.Parameter(1)
    public String catPath;

    @Parameterized.Parameters()
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{
                {"/simple.dot", "/postar.cat"},
        });
    }

    @Test
    public void test() throws IOException {
        final File model = new File(getClass().getResource(modelPath).getFile());
        final File cat = new File(getClass().getResource(catPath).getFile());

        final Collection<GraphConstraint> mcm = CatDslManager.createMCM(cat);

        final CandidateExecutionGraph partialGraph = PartialGraphVisitor.getPartialGraph(model);

        var partialSolver = new PartialSolver<>(mcm, partialGraph, new Pattern2ExprCompiler(), new SATGraphSolver(Z3SolverFactory.getInstance().createSolver()));
        var solution = partialSolver.getSolution();
    }
}
