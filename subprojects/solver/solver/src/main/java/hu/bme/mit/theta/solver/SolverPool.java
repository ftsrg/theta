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
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

public class SolverPool implements AutoCloseable {

    private static final int STARTING_SIZE = 10;
    private static final int GROWING = 5;

    private int created = 0;
    private long checkCount = 0;
    private static final boolean TRACE_CHECKS = false;

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
            final var solver = new CountingSolver(solverFactory.createSolver());
            this.available.add(solver);
            this.all.add(solver);
        }
        this.closingMode = closingMode;
    }

    public Solver requestSolver() {
        if (this.available.isEmpty()) createNewSolvers();
        return this.available.removeFirst();
    }

    public void returnSolver(Solver solver) {
        Preconditions.checkState(
                solver.getAssertions().isEmpty(), "Only empty solvers can be returned");
        this.available.add(solver);
    }

    private void createNewSolvers() {
        for (int i = 0; i < GROWING; i++) {
            final var solver = new CountingSolver(solverFactory.createSolver());
            this.available.add(solver);
            this.all.add(solver);
        }
        this.created = created + GROWING;
    }

    public int size() {
        return this.created;
    }

    public long getCheckCount() {
        return checkCount;
    }

    @Override
    public void close() throws Exception {
        if (closingMode == ClosingMode.ALL) {
            for (Solver solver : all) solver.close();
        } else {
            for (Solver solver : available) solver.close();
        }
        this.available.clear();
        this.all.clear();
        this.created = 0;
    }

    private class CountingSolver implements Solver {

        private final Solver wrapped;

        CountingSolver(Solver wrapped) {
            this.wrapped = wrapped;
        }

        @Override
        public SolverStatus check() {
            checkCount++;
            if (TRACE_CHECKS) {
                var caller = Thread.currentThread().getStackTrace()[2];
                System.err.println(
                        "SolverPool.check() #"
                                + checkCount
                                + " from "
                                + caller.getClassName()
                                + "."
                                + caller.getMethodName()
                                + ":"
                                + caller.getLineNumber());
            }
            return wrapped.check();
        }

        @Override
        public void add(Expr<BoolType> assertion) {
            wrapped.add(assertion);
        }

        @Override
        public void push() {
            wrapped.push();
        }

        @Override
        public void pop(int n) {
            wrapped.pop(n);
        }

        @Override
        public void reset() {
            wrapped.reset();
        }

        @Override
        public SolverStatus getStatus() {
            return wrapped.getStatus();
        }

        @Override
        public Valuation getModel() {
            return wrapped.getModel();
        }

        @Override
        public Collection<Expr<BoolType>> getAssertions() {
            return wrapped.getAssertions();
        }

        @Override
        public ImmutableMap<String, String> getStatistics() {
            return wrapped.getStatistics();
        }

        @Override
        public Expr<BoolType> simplify(Expr<BoolType> expr) {
            return wrapped.simplify(expr);
        }

        @Override
        public void close() throws Exception {
            wrapped.close();
        }
    }
}
