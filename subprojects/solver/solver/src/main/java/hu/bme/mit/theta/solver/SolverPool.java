/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver;

import com.google.common.base.Preconditions;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class SolverPool implements AutoCloseable {

    private static final int STARTING_SIZE = 10;
    private static final int GROWING = 5;

    private int created = 0;

    private final LinkedList<Solver> available;
    private final List<Solver> all;

    private final SolverFactory solverFactory;

    public enum ClosingMode {
        ALL,
        RETURNED
    }

    private final ClosingMode closingMode;

    public SolverPool(SolverFactory solverFactory) {
        this(solverFactory, ClosingMode.ALL);
    }

    public SolverPool(SolverFactory solverFactory, ClosingMode closingMode) {
        this.solverFactory = solverFactory;
        this.available = new LinkedList<>();
        this.all = new ArrayList<>();
        for (int i = 0; i < STARTING_SIZE; i++) {
            final var solver = solverFactory.createSolver();
            this.available.add(solver);
            this.all.add(solver);
        }
        this.closingMode = closingMode;
    }

    public Solver requestSolver() {
        if (this.available.isEmpty()) createNewSolvers();
        return this.available.removeAt(0);
    }

    public void returnSolver(Solver solver) {
        Preconditions.checkState(
                solver.getAssertions().isEmpty(), "Only empty solvers can be returned");
        //        System.out.println("Returned solver");
        this.available.add(solver);
    }

    private void createNewSolvers() {
        for (int i = 0; i < GROWING; i++) {
            final var solver = solverFactory.createSolver();
            this.available.add(solver);
            this.all.add(solver);
        }
        //        System.out.println(created + " solvers created");
        //        System.out.println("Free size: " + Runtime.getRuntime().freeMemory());
        this.created = created + GROWING;
    }

    public int size() {
        return this.created;
    }

    @Override
    public void close() throws Exception {
        //        System.out.println(all.size() - available.size() + " solvers not returned");
        if (closingMode == ClosingMode.ALL) {
            for (Solver solver : all) solver.close();
            //            System.out.println("Closed " + all.size() + " solvers");
        } else {
            for (Solver solver : available) solver.close();
            //            System.out.println("Closed " + available.size() + " solvers");
        }
        this.available.clear();
        this.all.clear();
        this.created = 0;
    }
}
