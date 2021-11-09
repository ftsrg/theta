package hu.bme.mit.theta.xcfa.analysis.utils;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class XcfaTraceConcretizer {
	public static Trace<XcfaState<ExplState>, XcfaAction> concretize(
			final Trace<XcfaState<?>, XcfaAction> trace, SolverFactory solverFactory) {
		List<XcfaState<?>> sbeStates = new ArrayList<>();
		List<XcfaAction> sbeActions = new ArrayList<>();

		sbeStates.add(trace.getState(0));
		for (int i = 0; i < trace.getActions().size(); ++i) {
			final XcfaEdge edge = XcfaEdge.of(trace.getAction(i).getSource(), trace.getAction(i).getTarget(), trace.getAction(i).getLabels());
			sbeActions.add(XcfaAction.create(edge));
			sbeStates.add(trace.getState(i+1));
		}
		Trace<XcfaState<?>, XcfaAction> sbeTrace = Trace.of(sbeStates, sbeActions);
		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
				BoolExprs.True(), solverFactory.createItpSolver());
		final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
		checkArgument(status.isFeasible(), "Infeasible trace.");
		final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

		assert valuations.getStates().size() == sbeTrace.getStates().size();

		final List<XcfaState<ExplState>> cfaStates = new ArrayList<>();
		for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
			cfaStates.add(XcfaState.create(sbeTrace.getState(i).getCurrentLoc(), ExplState.of(valuations.getState(i))));
		}

		return Trace.of(cfaStates, sbeTrace.getActions());
	}

}
