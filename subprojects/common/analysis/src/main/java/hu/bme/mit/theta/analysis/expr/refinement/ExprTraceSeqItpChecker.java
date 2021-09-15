/*
 *  Copyright 2017 Budapest University of Technology and Economics
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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * An ExprTraceChecker that generates a sequence interpolant by checking the
 * trace at once.
 */
public final class ExprTraceSeqItpChecker implements ExprTraceChecker<ItpRefutation> {

	private final ItpSolver solver;
	private final Expr<BoolType> init;
	private final Expr<BoolType> target;

	private ExprTraceSeqItpChecker(final Expr<BoolType> init, final Expr<BoolType> target, final ItpSolver solver) {
		this.solver = checkNotNull(solver);
		this.init = checkNotNull(init);
		this.target = checkNotNull(target);
	}

	public static ExprTraceSeqItpChecker create(final Expr<BoolType> init, final Expr<BoolType> target,
												final ItpSolver solver) {
		return new ExprTraceSeqItpChecker(init, target, solver);
	}

	@Override
	public ExprTraceStatus<ItpRefutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		checkNotNull(trace);
		final int stateCount = trace.getStates().size();

		try (WithPushPop wpp = new WithPushPop(solver)) {
			final List<ItpMarker> markers = new ArrayList<>(stateCount + 1);
			for (int i = 0; i < stateCount + 1; ++i) {
				markers.add(solver.createMarker());
			}
			final ItpPattern pattern = solver.createSeqPattern(markers);

			final List<VarIndexing> indexings = new ArrayList<>(stateCount);
			indexings.add(VarIndexingFactory.indexing(0));

			solver.add(markers.get(0), PathUtils.unfold(init, indexings.get(0)));
			solver.add(markers.get(0), PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0)));
			assert solver.check().isSat() : "Initial state of the trace is not feasible";

			for (int i = 1; i < stateCount; ++i) {
				indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
				solver.add(markers.get(i), PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i)));
				solver.add(markers.get(i), PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1)));
			}

			solver.add(markers.get(trace.getStates().size()), PathUtils.unfold(target, indexings.get(stateCount - 1)));
			final boolean concretizable = solver.check().isSat();

			if (concretizable) {
				final Valuation model = solver.getModel();
				final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
				for (final VarIndexing indexing : indexings) {
					builder.add(PathUtils.extractValuation(model, indexing));
				}
				return ExprTraceStatus.feasible(Trace.of(builder.build(), trace.getActions()));
			} else {
				final List<Expr<BoolType>> interpolants = new ArrayList<>();
				final Interpolant interpolant = solver.getInterpolant(pattern);
				for (int i = 0; i < markers.size() - 1; ++i) {
					interpolants.add(PathUtils.foldin(interpolant.eval(markers.get(i)), indexings.get(i)));
				}
				return ExprTraceStatus.infeasible(ItpRefutation.sequence(interpolants));
			}
		}
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
