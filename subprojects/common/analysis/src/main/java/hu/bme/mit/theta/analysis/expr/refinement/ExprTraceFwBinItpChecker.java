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

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * An ExprTraceChecker that generates a binary interpolant by incrementally
 * checking the counterexample forward.
 */
public final class ExprTraceFwBinItpChecker implements ExprTraceChecker<ItpRefutation> {

	private final ItpSolver solver;
	private final Expr<BoolType> init;
	private final Expr<BoolType> target;

	private ExprTraceFwBinItpChecker(final Expr<BoolType> init, final Expr<BoolType> target, final ItpSolver solver) {
		this.solver = checkNotNull(solver);
		this.init = checkNotNull(init);
		this.target = checkNotNull(target);
	}

	public static ExprTraceFwBinItpChecker create(final Expr<BoolType> init, final Expr<BoolType> target,
												  final ItpSolver solver) {
		return new ExprTraceFwBinItpChecker(init, target, solver);
	}

	@Override
	public ExprTraceStatus<ItpRefutation> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		checkNotNull(trace);
		final int stateCount = trace.getStates().size();

		final List<VarIndexing> indexings = new ArrayList<>(stateCount);
		indexings.add(VarIndexingFactory.indexing(0));

		solver.push();

		final ItpMarker A = solver.createMarker();
		final ItpMarker B = solver.createMarker();
		final ItpPattern pattern = solver.createBinPattern(A, B);

		int nPush = 1;
		solver.add(A, PathUtils.unfold(init, indexings.get(0)));
		solver.add(A, PathUtils.unfold(trace.getState(0).toExpr(), indexings.get(0)));
		assert solver.check().isSat() : "Initial state of the trace is not feasible";
		int satPrefix = 0;

		for (int i = 1; i < stateCount; ++i) {
			solver.push();
			++nPush;
			indexings.add(indexings.get(i - 1).add(trace.getAction(i - 1).nextIndexing()));
			solver.add(A, PathUtils.unfold(trace.getState(i).toExpr(), indexings.get(i)));
			solver.add(A, PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings.get(i - 1)));

			if (solver.check().isSat()) {
				satPrefix = i;
			} else {
				solver.pop();
				--nPush;
				break;
			}
		}

		final boolean concretizable;

		if (satPrefix == stateCount - 1) {
			solver.add(B, PathUtils.unfold(target, indexings.get(stateCount - 1)));
			concretizable = solver.check().isSat();
		} else {
			solver.add(B, PathUtils.unfold(trace.getState(satPrefix + 1).toExpr(), indexings.get(satPrefix + 1)));
			solver.add(B, PathUtils.unfold(trace.getAction(satPrefix).toExpr(), indexings.get(satPrefix)));
			solver.check();
			assert solver.getStatus().isUnsat() : "Trying to interpolate a feasible formula";
			concretizable = false;
		}

		ExprTraceStatus<ItpRefutation> status = null;
		if (concretizable) {
			final Valuation model = solver.getModel();
			final ImmutableList.Builder<Valuation> builder = ImmutableList.builder();
			for (final VarIndexing indexing : indexings) {
				builder.add(PathUtils.extractValuation(model, indexing));
			}
			status = ExprTraceStatus.feasible(Trace.of(builder.build(), trace.getActions()));
		} else {
			final Interpolant interpolant = solver.getInterpolant(pattern);
			final Expr<BoolType> itpFolded = PathUtils.foldin(interpolant.eval(A), indexings.get(satPrefix));
			status = ExprTraceStatus.infeasible(ItpRefutation.binary(itpFolded, satPrefix, stateCount));
		}
		assert status != null;
		solver.pop(nPush);

		return status;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

}
