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
package hu.bme.mit.theta.solver.javasmt;

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
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

final class JavaSMTItpSolver implements ItpSolver, Solver {

    private final JavaSMTTransformationManager transformationManager;

    private final JavaSMTSolver solver;
    private final InterpolatingProverEnvironment interpolatingProverEnvironment;

    private final Stack<JavaSMTItpMarker> markers;

    private final JavaSMTTermTransformer termTransformer;

    public JavaSMTItpSolver(final JavaSMTSymbolTable symbolTable,
                            final JavaSMTTransformationManager transformationManager,
                            final JavaSMTTermTransformer termTransformer,
                            final SolverContext context,
                            final InterpolatingProverEnvironment interpolatingProverEnvironment) {
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;

        this.solver = new JavaSMTSolver(symbolTable, transformationManager, termTransformer, context, interpolatingProverEnvironment);
        this.interpolatingProverEnvironment = interpolatingProverEnvironment;

        markers = new StackImpl<>();
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
        final JavaSMTItpMarker z3Marker = (JavaSMTItpMarker) marker;
        BooleanFormula term = (BooleanFormula) transformationManager.toTerm(assertion);
        solver.add(assertion, term);
        z3Marker.add(assertion);
    }

    @Override
    public Interpolant getInterpolant(final ItpPattern pattern) {
        checkState(solver.getStatus() == SolverStatus.UNSAT,
                "Cannot get interpolant if status is not UNSAT.");
        checkArgument(pattern instanceof JavaSMTItpPattern);
        final List<JavaSMTItpMarker> z3ItpPattern = ((JavaSMTItpPattern) pattern).getSequence();

        try {
            final List<BooleanFormula> interpolants = interpolatingProverEnvironment.getSeqInterpolants(z3ItpPattern.stream().
                    map(javaSMTItpMarker -> javaSMTItpMarker.getTerms().stream().
                            map(transformationManager::toTerm).toList()).
                    toList());
            Map<ItpMarker, Expr<BoolType>> itpMap = Containers.createMap();
            for (int i = 0; i < interpolants.size(); i++) {
                BooleanFormula term = interpolants.get(i);
                Expr<BoolType> expr = (Expr<BoolType>) termTransformer.toExpr(term);
                itpMap.put(z3ItpPattern.get(i), expr);
            }
            return new JavaSMTInterpolant(itpMap);
        } catch (SolverException | InterruptedException e) {
            throw new JavaSMTSolverException(e);
        }
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
        markers.push();
        for (final JavaSMTItpMarker marker : markers) {
            marker.push();
        }
        solver.push();
    }

    @Override
    public void pop(final int n) {
        markers.pop(n);
        for (final JavaSMTItpMarker marker : markers) {
            marker.pop(n);
        }
        solver.pop(n);
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
    public void close() {
        solver.close();
    }
}
