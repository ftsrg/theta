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

package hu.bme.mit.theta.solver.validator;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;

import java.util.Collection;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class ItpSolverValidatorWrapper implements ItpSolver {

    private final ItpSolver solver;

    ItpSolverValidatorWrapper(String solver) throws Exception {
        this.solver = SolverManager.resolveSolverFactory(solver).createItpSolver();
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {
        return solver.createTreePattern(root);
    }

    @Override
    public ItpMarker createMarker() {
        return solver.createMarker();
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        solver.add(marker, assertion);
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        return solver.getInterpolant(pattern);
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return solver.getMarkers();
    }

    @Override
    public SolverStatus check() {
        SolverStatus check = solver.check();
        if (check.isSat()) {
            final Valuation model = solver.getModel();
            for (Expr<BoolType> assertion : solver.getAssertions()) {
                if (!assertion.eval(model).equals(True())) {
                    throw new RuntimeException("Solver problem: " + assertion);
                }
            }
        }
        return check;
    }

    @Override
    public void push() {
        solver.push();
    }

    @Override
    public void pop(int n) {
        solver.pop();
    }

    @Override
    public void reset() {
        solver.reset();
    }

    @Override
    public SolverStatus getStatus() {
        return solver.getStatus();
    }

    @Override
    public Valuation getModel() {
        return solver.getModel();
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return solver.getAssertions();
    }

    @Override
    public void close() throws Exception {
        solver.close();
    }
}
