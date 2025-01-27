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
package hu.bme.mit.theta.solver.javasmt;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

final class JavaSMTItpSolver implements ItpSolver, Solver {

    private final JavaSMTTransformationManager transformationManager;

    private final JavaSMTSolver solver;
    private final InterpolatingProverEnvironment interpolatingProverEnvironment;

    private final Stack<JavaSMTItpMarker> markers;
    private final Stack<Tuple2<Expr<BoolType>, Object>> termMap;
    private Map<Expr<BoolType>, Object> combinedTermMap = Map.of();

    private final JavaSMTTermTransformer termTransformer;
    private final SolverContext context;
		
	 	private int expCnt = 0;

    public JavaSMTItpSolver(
            final JavaSMTSymbolTable symbolTable,
            final JavaSMTTransformationManager transformationManager,
            final JavaSMTTermTransformer termTransformer,
            final SolverContext context,
            final InterpolatingProverEnvironment interpolatingProverEnvironment) {
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.context = context;

        this.solver =
                new JavaSMTSolver(
                        symbolTable,
                        transformationManager,
                        termTransformer,
                        context,
                        interpolatingProverEnvironment);
        this.interpolatingProverEnvironment = interpolatingProverEnvironment;

        markers = new StackImpl<>();
        termMap = new StackImpl<>();
    }

    @Override
    public ItpPattern createTreePattern(final ItpMarkerTree<? extends ItpMarker> root) {
        checkNotNull(root);
        return JavaSMTItpPattern.of(root);
    }

    @Override
    public JavaSMTItpMarker createMarker() {
        final JavaSMTItpMarker marker = new JavaSMTItpMarker();
        markers.add(marker);
        return marker;
    }

    @Override
    public void add(final ItpMarker marker, final Expr<BoolType> assertion) {
        checkNotNull(marker);
        checkNotNull(assertion);
        checkArgument(markers.toCollection().contains(marker), "Marker not found in solver");
        final JavaSMTItpMarker jsmtMarker = (JavaSMTItpMarker) marker;
        BooleanFormula term = (BooleanFormula) transformationManager.toTerm(assertion);
        if (!combinedTermMap.containsKey(assertion)) { // otherwise assertions are overridden
            Object c = solver.add(assertion, term);
            jsmtMarker.add(c);
            termMap.add(Tuple2.of(assertion, c));
            combinedTermMap =
                    termMap.toCollection().stream()
                            .collect(Collectors.toMap(Tuple2::get1, Tuple2::get2));
        } else {
            jsmtMarker.add(combinedTermMap.get(assertion));
        }
    }

    @Override
    public Interpolant getInterpolant(final ItpPattern pattern) {
        checkState(
                solver.getStatus() == SolverStatus.UNSAT,
                "Cannot get interpolant if status is not UNSAT.");
        checkArgument(pattern instanceof JavaSMTItpPattern);

        checkArgument(pattern instanceof JavaSMTItpPattern);
        final JavaSMTItpPattern javaSMTItpPattern = (JavaSMTItpPattern) pattern;

        final List<JavaSMTItpMarker> markerList = new LinkedList<>();
        final List<Collection<?>> termList = new LinkedList<>();
        final List<Integer> indexList = new LinkedList<>();

        getInterpolantParams(javaSMTItpPattern.getRoot(), markerList, termList, indexList);

        try {
            final List<BooleanFormula> interpolants;
            if (indexList.stream().allMatch(i -> i == 0)) {
                interpolants = interpolatingProverEnvironment.getSeqInterpolants(termList);
            } else {
                interpolants =
                        interpolatingProverEnvironment.getTreeInterpolants(
                                termList, indexList.stream().mapToInt(i -> i).toArray());
            }

            Map<ItpMarker, Expr<BoolType>> itpMap = Containers.createMap();
            for (int i = 0; i < interpolants.size(); i++) {
                BooleanFormula term = interpolants.get(i);
                Expr<BoolType> expr = (Expr<BoolType>) termTransformer.toExpr(term);
                itpMap.put(markerList.get(i), expr);
            }
            itpMap.put(markerList.get(interpolants.size()), False());
            return new JavaSMTInterpolant(itpMap);
        } catch (SolverException | InterruptedException e) {
            throw new JavaSMTSolverException(e);
        }
    }

    private int getInterpolantParams(
            final ItpMarkerTree<JavaSMTItpMarker> root,
            List<JavaSMTItpMarker> markerList,
            final List<Collection<?>> terms,
            final List<Integer> indices) {
        int leftmostIndex = -1;
        for (ItpMarkerTree<JavaSMTItpMarker> child : root.getChildren()) {
            final int index = getInterpolantParams(child, markerList, terms, indices);
            if (leftmostIndex == -1) {
                leftmostIndex = index;
            }
        }
        if (leftmostIndex == -1) {
            leftmostIndex = indices.size();
        }
        markerList.add(root.getMarker());
        terms.add(root.getMarker().getTerms());
        indices.add(leftmostIndex);
        return leftmostIndex;
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    // delegate

    @Override
    public void add(final Expr<BoolType> assertion) {
        checkNotNull(assertion);
        solver.add(assertion);
    }

    @Override
    public SolverStatus check() {
        return solver.check();
    }

    @Override
    public void push() {
				expCnt++;
        markers.push();
        termMap.push();
        for (final JavaSMTItpMarker marker : markers) {
            marker.push();
        }
        solver.push();
        combinedTermMap =
                termMap.toCollection().stream()
                        .collect(Collectors.toMap(Tuple2::get1, Tuple2::get2));
    }

    @Override
    public void pop(final int n) {
				expCnt-=n;
        markers.pop(n);
        termMap.pop(n);
        for (final JavaSMTItpMarker marker : markers) {
            marker.pop(n);
        }
        solver.pop(n);
        combinedTermMap =
                termMap.toCollection().stream()
                        .collect(Collectors.toMap(Tuple2::get1, Tuple2::get2));
    }

		@Override 
		public void popAll() {
				pop(expCnt);
		}

    @Override
    public void reset() {
        solver.reset();
				expCnt = 0;
        combinedTermMap = Map.of();
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
    public void close() {
        solver.close();
    }
}
