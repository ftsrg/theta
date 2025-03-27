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
package hu.bme.mit.theta.solver.meta;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkState;


class MetaSolver implements  Solver {

    private Solver solver;
    private final Solver z3 = Z3SolverFactory.getInstance().createSolver();
    private final Solver z3Legacy = Z3LegacySolverFactory.getInstance().createSolver();
    private final Stack<Expr<BoolType>> assertions = new StackImpl<>();

    MetaSolver() {
        solver = z3Legacy;
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        assertions.add(assertion);
        try {
            solver.add(assertion);
        }
        catch (Exception e) {
            switchSolvers();
        }

    }

    @Override
    public SolverStatus check() {
        try {
            return solver.check();
        }
        catch (Exception e) {
            switchSolvers();
            return check();
        }
    }

    @Override
    public void push() {
        solver.push();
    }

    @Override
    public void pop(int n) {
        solver.pop(n);
    }

    @Override
    public void reset() {
        z3.reset();
        z3Legacy.reset();
        solver = z3Legacy;
    }

    @Override
    public SolverStatus getStatus() {
        try {
            return solver.getStatus();
        }
        catch (Exception e) {
            switchSolvers();
            return getStatus();
        }
    }

    @Override
    public Valuation getModel() {
        try {
            return solver.getModel();
        }
        catch (Exception e) {
            switchSolvers();
            return getModel();
        }
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return solver.getAssertions();
    }

    @Override
    public void close() throws Exception {
        z3.close();
        z3Legacy.close();
    }

    private void switchSolvers() {
        checkState(solver != z3, "Metasolver has cycled through all of its solvers.");

        solver = z3;
        for (Expr<BoolType> assertion : assertions) {
            solver.add(assertion);
        }
    }
}
