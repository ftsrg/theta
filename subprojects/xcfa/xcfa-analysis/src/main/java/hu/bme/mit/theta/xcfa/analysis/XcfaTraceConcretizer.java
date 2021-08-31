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
package hu.bme.mit.theta.xcfa.analysis;

public final class XcfaTraceConcretizer {

	private XcfaTraceConcretizer() {
	}
//
//	public static Trace<XcfaState<ExplState>, XcfaAction> concretize(
//			final Trace<XcfaState<?>, XcfaAction> trace, SolverFactory solverFactory) {
//		throw new RuntimeException("Not yet implemented!");
//		List<XcfaState<?>> sbeStates = new ArrayList<>();
//		List<XcfaAction> sbeActions = new ArrayList<>();
//
//		sbeStates.add(trace.getState(0));
//		for (int i = 0; i < trace.getActions().size(); ++i) {
//			XcfaEdge edge = trace.getAction(i).getEdge();
//			sbeActions.add(XcfaAction.create(edge));
//			sbeStates.add(trace.getState(i+1));
//		}
//		Trace<XcfaState<?>, XcfaAction> sbeTrace = Trace.of(sbeStates, sbeActions);
//		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
//				BoolExprs.True(), solverFactory.createItpSolver());
//		final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
//		checkArgument(status.isFeasible(), "Infeasible trace.");
//		final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();
//
//		assert valuations.getStates().size() == sbeTrace.getStates().size();
//
//		final List<XcfaState<ExplState>> xcfaStates = new ArrayList<>();
//		for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
//			xcfaStates.add(XcfaState.of(sbeTrace.getState(i).getLoc(), ExplState.of(valuations.getState(i))));
//		}
//
//		return Trace.of(xcfaStates, sbeTrace.getActions());
//	}
}
