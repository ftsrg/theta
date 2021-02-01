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
package hu.bme.mit.theta.cfa.analysis;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.SolverFactory;

public final class CfaTraceConcretizer {

	private CfaTraceConcretizer() {
	}

	public static Trace<CfaState<ExplState>, CfaAction> concretize(
			final Trace<CfaState<?>, CfaAction> trace, SolverFactory solverFactory) {
		List<CfaState<?>> sbeStates = new ArrayList<>();
		List<CfaAction> sbeActions = new ArrayList<>();

		sbeStates.add(trace.getState(0));
		for (int i = 0; i < trace.getActions().size(); ++i) {
			List<CFA.Edge> edges = trace.getAction(i).getEdges();
			sbeActions.add(CfaAction.create(edges.get(0)));
			for (int e = 1; e < edges.size(); ++e) {
				sbeStates.add(CfaState.of(edges.get(e).getSource(), ExplState.top()));
				sbeActions.add(CfaAction.create(edges.get(e)));
			}
			sbeStates.add(trace.getState(i+1));
		}
		Trace<CfaState<?>, CfaAction> sbeTrace = Trace.of(sbeStates, sbeActions);
		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
				BoolExprs.True(), solverFactory.createItpSolver());
		final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
		checkArgument(status.isFeasible(), "Infeasible trace.");
		final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

		assert valuations.getStates().size() == sbeTrace.getStates().size();

		final List<CfaState<ExplState>> cfaStates = new ArrayList<>();
		for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
			cfaStates.add(CfaState.of(sbeTrace.getState(i).getLoc(), ExplState.of(valuations.getState(i))));
		}

		return Trace.of(cfaStates, sbeTrace.getActions());
	}
}
