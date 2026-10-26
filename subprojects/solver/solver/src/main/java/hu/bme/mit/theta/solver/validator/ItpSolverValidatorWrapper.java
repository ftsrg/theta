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
package hu.bme.mit.theta.solver.validator;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.UnknownSolverStatusException;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Validates the models of satisfiable checks, and every interpolant against a plain solver of the
 * same kind: a node's interpolant must follow from the assertions of its subtree and contradict all
 * the other assertions. Either failure is reported as a solver problem.
 */
public class ItpSolverValidatorWrapper implements ItpSolver {

    private final ItpSolver solver;
    private final Solver checker;
    private final Stack<Tuple2<ItpMarker, Expr<BoolType>>> assertions = new StackImpl<>();

    ItpSolverValidatorWrapper(String solver) throws Exception {
        final SolverFactory factory = SolverManager.resolveSolverFactory(solver);
        this.solver = factory.createItpSolver();
        this.checker = factory.createSolver();
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
        assertions.add(Tuple2.of(marker, assertion));
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        final Interpolant interpolant = solver.getInterpolant(pattern);
        // the root's interpolant is False by definition, and some backends leave it out
        for (final ItpMarkerTree<?> child : asTree(pattern).getChildren()) {
            validate(child, interpolant);
        }
        return interpolant;
    }

    private Set<ItpMarker> validate(ItpMarkerTree<?> node, Interpolant interpolant) {
        final Set<ItpMarker> subtree = new HashSet<>();
        subtree.add(node.getMarker());
        for (final ItpMarkerTree<?> child : node.getChildren()) {
            subtree.addAll(validate(child, interpolant));
        }
        final List<Expr<BoolType>> inside = new ArrayList<>();
        final List<Expr<BoolType>> outside = new ArrayList<>();
        for (final Tuple2<ItpMarker, Expr<BoolType>> assertion : assertions) {
            (subtree.contains(assertion.get1()) ? inside : outside).add(assertion.get2());
        }
        final Expr<BoolType> itp = interpolant.eval(node.getMarker());
        inside.add(Not(itp));
        outside.add(itp);
        if (isSat(inside)) {
            throw new RuntimeException("Solver problem: interpolant not implied: " + itp);
        }
        if (isSat(outside)) {
            throw new RuntimeException("Solver problem: interpolant not refuting: " + itp);
        }
        return subtree;
    }

    /** An unknown result counts as unsatisfiable: only a definite model flags an interpolant. */
    private boolean isSat(List<Expr<BoolType>> exprs) {
        checker.push();
        try {
            checker.add(exprs);
            return checker.check().isSat();
        } catch (UnknownSolverStatusException e) {
            return false;
        } finally {
            checker.pop();
        }
    }

    private static ItpMarkerTree<?> asTree(ItpPattern pattern) {
        return pattern.visit(
                new ItpPattern.ItpPatternVisitor<ItpMarkerTree<?>>() {
                    @Override
                    public ItpMarkerTree<?> visitBinaryPattern(ItpPattern.Binary<?> binary) {
                        return ItpMarkerTree.<ItpMarker>Tree(
                                binary.getB(), ItpMarkerTree.Leaf(binary.getA()));
                    }

                    @Override
                    public ItpMarkerTree<?> visitSequencePattern(ItpPattern.Sequence<?> sequence) {
                        ItpMarkerTree<ItpMarker> tree = null;
                        for (final ItpMarker marker : sequence.getSequence()) {
                            tree =
                                    tree == null
                                            ? ItpMarkerTree.Leaf(marker)
                                            : ItpMarkerTree.Tree(marker, tree);
                        }
                        return tree;
                    }

                    @Override
                    public ItpMarkerTree<?> visitTreePattern(ItpPattern.Tree<?> tree) {
                        return tree.getRoot();
                    }
                });
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
        assertions.push();
    }

    @Override
    public void pop(int n) {
        solver.pop(n);
        assertions.pop(n);
    }

    @Override
    public void reset() {
        solver.reset();
        assertions.clear();
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
        checker.close();
    }
}
