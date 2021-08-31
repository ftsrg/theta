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
package hu.bme.mit.theta.xcfa.analysis.impact;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.BasicMultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.BasicStackableExprState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprTraceUtils;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaLocationState;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public final class PredImpactRefiner implements ImpactRefiner<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction> {

	private final ExprTraceSeqItpChecker traceChecker;

	private PredImpactRefiner(final ItpSolver solver) {
		checkNotNull(solver);
		traceChecker = ExprTraceSeqItpChecker.create(True(), True(), solver);
	}

	public static PredImpactRefiner create(final ItpSolver solver) {
		return new PredImpactRefiner(solver);
	}

	@Override
	public RefinementResult<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction> refine(final Trace<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction> cex) {
		final List<XcfaAction> actions = cex.getActions();

		final Trace<ExprState, ExprAction> exprTrace = ExprTraceUtils.traceFrom(actions);
		final ExprTraceStatus<ItpRefutation> traceStatus = traceChecker.check(exprTrace);

		if (traceStatus.isFeasible()) {
			return RefinementResult.unsuccesful();

		} else if (traceStatus.isInfeasible()) {
			final ItpRefutation refuation = traceStatus.asInfeasible().getRefutation();
			final List<Expr<BoolType>> exprs = refuation.toList();

			final List<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>> refinedStates = new ArrayList<>();
			for (int i = 0; i < exprs.size(); i++) {
				final XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>> state = cex.getState(i);
				final Expr<BoolType> expr = exprs.get(i);

				Map<Integer, BasicStackableExprState<XcfaLocationState<PredState>>> newThreadStates = new LinkedHashMap<>();
				for (Map.Entry<Integer, BasicStackableExprState<XcfaLocationState<PredState>>> entry : state.getState().getStates().entrySet()) {
					BasicStackableExprState<XcfaLocationState<PredState>> ss = entry.getValue();
					final List<XcfaLocationState<PredState>> newStates = new ArrayList<>();
					for (XcfaLocationState<PredState> s : ss.getStates()) {
						final List<Expr<BoolType>> newPreds = new ArrayList<>();
						newPreds.addAll(s.getState().getPreds());
						newPreds.add(expr);
						XcfaLocationState<PredState> s1 = s.withState(PredState.of(newPreds));
						newStates.add(s1);
					}
					BasicStackableExprState<XcfaLocationState<PredState>> ss1 = BasicStackableExprState.of(newStates);
					newThreadStates.put(entry.getKey(), ss1);
				}

				final XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>> refinedState = state.withState(BasicMultiStackableExprState.of(newThreadStates));

				refinedStates.add(refinedState);
			}

			final Trace<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction> trace = Trace.of(refinedStates, actions);
			return RefinementResult.succesful(trace);
		} else {
			throw new AssertionError();
		}
	}

}
