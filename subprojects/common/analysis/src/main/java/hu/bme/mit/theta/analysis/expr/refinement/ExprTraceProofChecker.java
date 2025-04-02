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
package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.IndexedVars;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.ProofNode;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/** An ExprTraceChecker that generates an unsat core by checking the trace at once. */
public final class ExprTraceProofChecker implements ExprTraceChecker<VarsRefutation> {

    private final Solver solver;
    private final Expr<BoolType> init;
    private final Expr<BoolType> target;

    private ExprTraceProofChecker(
            final Expr<BoolType> init, final Expr<BoolType> target, final Solver solver) {
        this.solver = checkNotNull(solver);
        this.init = checkNotNull(init);
        this.target = checkNotNull(target);
    }

    public static ExprTraceProofChecker create(
            final Expr<BoolType> init, final Expr<BoolType> target, final Solver solver) {
        return new ExprTraceProofChecker(init, target, solver);
    }

    @Override
    public ExprTraceStatus<VarsRefutation> check(
            final Trace<? extends ExprState, ? extends ExprAction> trace) {
        checkNotNull(trace);
        final int stateCount = trace.getStates().size();

        final List<VarIndexing> indexings = new ArrayList<>(stateCount);
        indexings.add(VarIndexingFactory.indexing(0));

        try (WithPushPop wpp = new WithPushPop(solver)) {
            solver.add(ExprUtils.getConjuncts(PathUtils.unfold(init, indexings.get(0))));
            solver.add(
                    ExprUtils.getConjuncts(
                            PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0))));
            assert solver.check().isSat() : "Initial state of the trace is not feasible";
            boolean concretizable = true;

            for (int i = 1; i < stateCount; ++i) {
                indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
                solver.add(
                        ExprUtils.getConjuncts(
                                PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i))));
                solver.add(
                        ExprUtils.getConjuncts(
                                PathUtils.unfold(
                                        trace.getAction(i - 1).toExpr(), indexings.get(i - 1))));

                if (!solver.check().isSat()) {
                    concretizable = false;
                    break;
                }
            }

            if (concretizable) {
                solver.add(
                        ExprUtils.getConjuncts(
                                PathUtils.unfold(target, indexings.get(stateCount - 1))));
                concretizable = solver.check().isSat();
            }

            if (concretizable) {
                final Valuation model = solver.getModel();
                final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
                for (final VarIndexing indexing : indexings) {
                    builder.add(PathUtils.extractValuation(model, indexing));
                }
                return ExprTraceStatus.feasible(Trace.of(builder.build(), trace.getActions()));
            } else {
                Set<ProofNode> proofLevel = Set.of(solver.getProof());
                while (proofLevel.stream()
                        .allMatch(proofNode -> proofNode.expr().equals(False()))) {
                    proofLevel =
                            proofLevel.stream()
                                    .flatMap(proofNode -> proofNode.children().stream())
                                    .collect(Collectors.toSet());
                }
                final var reasons = proofLevel.stream().map(ProofNode::expr).toList();
                final IndexedVars indexedVars = ExprUtils.getVarsIndexed(reasons);
                return ExprTraceStatus.infeasible(VarsRefutation.create(indexedVars));
            }
        }
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }
}
