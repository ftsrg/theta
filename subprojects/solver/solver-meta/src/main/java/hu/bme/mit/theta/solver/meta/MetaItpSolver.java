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
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.impl.StackImpl;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

final class MetaItpSolver implements ItpSolver, Solver {
    private ItpSolver solver;
    private final List<ItpSolver> solvers;
    private int currentSolverIndex = 0;
    private final Stack<Expr<BoolType>> assertions = new StackImpl<>();
    private final Stack<ItpMarker> markers = new StackImpl<>();

    MetaItpSolver(List<ItpSolver> solvers) {
        this.solvers = solvers;
        solver = solvers.get(0);
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {

        try {
            return solver.createTreePattern(root);
        } catch (Exception e) {
            switchSolvers();
            return solver.createTreePattern(root);
        }
    }

    @Override
    public ItpMarker createMarker() {
        Map<ItpSolver, ItpMarker> markersMap = new HashMap<>();
        for (ItpSolver solver : solvers) {
            markersMap.put(solver, solver.createMarker());
        }
        ItpMarker marker = new  MetaItpMarker(markersMap);
        markers.add(marker);
        return marker;
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        checkArgument(marker instanceof MetaItpMarker);

        assertions.add(assertion);
        try {
            solver.add(((MetaItpMarker) marker).getMarker(solver), assertion);
        } catch (Exception e) {
            switchSolvers();
        }
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        try {
            return solver.getInterpolant(pattern);
        } catch (Exception e) {
            switchSolvers();
            check();
            return solver.getInterpolant(pattern);
        }
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return solver.getMarkers();
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
        for (ItpSolver itpSolver : solvers) {
            itpSolver.reset();
        }
        solver = solvers.get(0);
    }

    @Override
    public SolverStatus getStatus() {
        try {
            return solver.getStatus();
        }
        catch (Exception e) {
            switchSolvers();
            check();
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
        for (ItpSolver itpSolver : solvers) {
            itpSolver.close();
        }
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        assertions.add(assertion);
        try {
            ((Solver) solver).add(assertion);
        } catch (Exception e) {
            switchSolvers();
        }
    }

    private void switchSolvers() {
        checkState(currentSolverIndex != solvers.size(), "Meta ITP solver has cycled through all of its solvers.");
        try {
            solver.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        solver = solvers.get(++currentSolverIndex);

        for (Expr<BoolType> assertion : assertions) {
            solver.add(createMarker(), assertion);
        }
    }
}
