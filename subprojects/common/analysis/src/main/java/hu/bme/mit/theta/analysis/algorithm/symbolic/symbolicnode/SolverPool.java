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
package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.LinkedList;
import java.util.function.Supplier;

public class SolverPool implements AutoCloseable{

    private final static int STARTING_SIZE = 10;
    private final static int GROWING = 5;

    private int created = 0;

    private final LinkedList<Solver> available;

    private final SolverFactory solverFactory;

    public SolverPool(SolverFactory solverFactory) {
        this.solverFactory = solverFactory;
        this.available = new LinkedList<>();
        for (int i = 0; i < STARTING_SIZE; i++) this.available.add(solverFactory.createSolver());
    }

    public Solver requestSolver() {
        if (this.available.size() == 0) createNewSolvers();
        return this.available.removeFirst();
    }

    public void returnSolver(Solver solver) {
        Preconditions.checkState(solver.getAssertions().isEmpty(), "Only empty solvers can be returned");
        this.available.add(solver);
    }

    private void createNewSolvers() {
        for (int i = 0; i < GROWING; i++) this.available.add(solverFactory.createSolver());
        System.out.println(created + " solvers created");
        System.out.println("Free size: "+Runtime.getRuntime().freeMemory());
        this.created = created + GROWING;
    }

    public int size() {
        return this.created;
    }

    @Override
    public void close() throws Exception {
        for (Solver solver : available) solver.close();
        System.out.println(created - available.size() + " solvers not returned");
        this.available.clear();
        this.created = 0;
    }
}
