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
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;

import java.util.*;
import java.util.concurrent.*;

import static com.google.common.base.Preconditions.checkArgument;

public class MetaItpSolver implements ItpSolver, Solver {
    private final List<ItpSolver> solvers;
    private final Stack<Expr<BoolType>> assertions = new StackImpl<>();
    private final Stack<MetaItpMarker> markers = new StackImpl<>();
    private final List<MetaItpPattern> patterns = new ArrayList<>();

    public MetaItpSolver(List<ItpSolver> solvers) {
        this.solvers = solvers;
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {
        Map<ItpSolver, ItpPattern> patternMap = new HashMap<>();
        // copy tree for each solver
        List<SolverResult<ItpMarkerTree<ItpMarker>>> solverResultList = allResults(solver -> new SolverResult<>(copyTree(root, solver), solver));
        for (final SolverResult<ItpMarkerTree<ItpMarker>> result : solverResultList) {
            patternMap.put(result.solver, result.solver.createTreePattern(result.result));
        }
        MetaItpPattern pattern = new MetaItpPattern(patternMap);
        patterns.add(pattern);
        return pattern;
    }

    private ItpMarkerTree<ItpMarker> copyTree(ItpMarkerTree<? extends ItpMarker> root, ItpSolver solver) {
        checkArgument(root.getMarker() instanceof MetaItpMarker);
        final MetaItpMarker metaMarker = (MetaItpMarker) root.getMarker();
        final ItpMarker marker = metaMarker.getMarker(solver);
        if (root.getChildrenNumber() == 0) {
            return ItpMarkerTree.Leaf(marker);
        }
        ItpMarkerTree<ItpMarker>[] subtrees = (ItpMarkerTree<ItpMarker>[]) root.getChildren().stream()
                .map(child -> copyTree(child,solver))
                .toArray();
        return ItpMarkerTree.Tree(marker, subtrees);
    }

    @Override
    public ItpMarker createMarker() {
        Map<ItpSolver, ItpMarker> markersMap = new HashMap<>();
        for (ItpSolver solver : solvers) {
            markersMap.put(solver, solver.createMarker());
        }
        MetaItpMarker marker = new MetaItpMarker(markersMap);
        markers.add(marker);
        return marker;
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        checkArgument(marker instanceof MetaItpMarker);

        assertions.add(assertion);
        for (ItpSolver solver : solvers) {
            try {
                solver.add(((MetaItpMarker) marker).getMarker(solver), assertion);
            } catch (Exception e) {
                remove(solver);
            }
        }

    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        checkArgument(pattern instanceof MetaItpPattern);

        List<SolverResult<Interpolant>> interpolants = allResults(solver ->
                new SolverResult<>(solver.getInterpolant(((MetaItpPattern) pattern).getPattern(solver)), solver));

        SolverResult<Interpolant> strongest = interpolants.stream().min(MetaItpSolver::selectStronger).orElseThrow();
        return new MetaInterpolant(strongest.solver, strongest.result);
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        assertions.add(assertion);
        for (ItpSolver solver : solvers) {
            try {
                ((Solver) solver).add(assertion);
            } catch (Exception e) {
                remove(solver);
            }
        }
    }

    @Override
    public SolverStatus check() {
        // wait for all the solvers to finish this step, so getting the model or interpolant is possible
        return allResults(SolverBase::check).get(0);
    }

    @Override
    public void push() {
        markers.push();
        for (ItpSolver solver : solvers) {
            solver.push();
        }
    }

    @Override
    public void pop(int n) {
        markers.pop(n);
        for (ItpSolver solver : solvers) {
            solver.pop(n);
        }
    }

    @Override
    public void reset() {
        for (ItpSolver solver : solvers) {
            solver.reset();
        }
    }

    @Override
    public SolverStatus getStatus() {
        return firstResult(SolverBase::getStatus);
    }

    @Override
    public Valuation getModel() {
        return firstResult(SolverBase::getModel);
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return assertions.toCollection();
    }

    @Override
    public void close() throws Exception {
        for (ItpSolver itpSolver : solvers) {
            itpSolver.close();
        }
    }

    private void remove(ItpSolver solver) {
        solvers.remove(solver);
        for (MetaItpPattern pattern : patterns) {
            pattern.remove(solver);
        }

        try {
            solver.reset();
            solver.close();
        } catch (Exception e) {
            throw new MetaSolverException("Closing solver failed", e);
        }
        checkArgument(!solvers.isEmpty(), "MetaItpSolver has run out of solvers.");
    }

    private interface SolverAction <T> {
        T run(ItpSolver solver);
    }

    private <T> T firstResult(SolverAction<T> action){
        ExecutorService executorService = Executors.newFixedThreadPool(solvers.size());
        List<Callable<T>> tasks = new ArrayList<>();

        for (ItpSolver solver : solvers) {
            tasks.add(() -> {
                T result;
                try {
                   result = action.run(solver);
                } catch (Exception e) {
                    remove(solver);
                    // ignore this task's result
                    throw new IllegalStateException();
                }
                return result;
            });
        }

        T item;
        try {
            item = executorService.invokeAny(tasks);
        } catch (ExecutionException | InterruptedException e) {
            throw new MetaSolverException(e);
        }
        return item;
    }

    private <T> List<T> allResults(SolverAction<T> action){
        ExecutorService executorService = Executors.newFixedThreadPool(solvers.size());
        List<Callable<T>> tasks = new ArrayList<>();

        for (ItpSolver solver : solvers) {
            tasks.add(() -> {
                T result = null;
                try {
                    result = action.run(solver);
                } catch (Exception e) {
                    remove(solver);
                }
                return result;
            });
        }

        List<Future<T>> futureItems;
        try {
            futureItems = executorService.invokeAll(tasks);
        } catch (InterruptedException e) {
            throw new MetaSolverException(e);
        }

        List<T> items = futureItems.stream()
                .map(future -> {
                    try {
                        return future.get();
                    } catch (InterruptedException | ExecutionException e) {
                        throw new MetaSolverException(e);
                    }
                })
                .filter(Objects::nonNull)
                .toList();

        executorService.shutdown();
        return items;
    }

    private static class SolverResult <T> {
        T result;
        ItpSolver solver;
        public SolverResult(T result, ItpSolver solver) {
            this.result = result;
            this.solver = solver;
        }
    }

    private static int selectStronger(SolverResult<Interpolant> a, SolverResult<Interpolant> b) {
        // todo choose strongest
        return 0;
    }
}
