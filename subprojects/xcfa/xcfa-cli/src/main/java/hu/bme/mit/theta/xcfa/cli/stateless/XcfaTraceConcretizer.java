package hu.bme.mit.theta.xcfa.cli.stateless;

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
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class XcfaTraceConcretizer {
	public static Trace<XcfaDeclarativeState<ExplState>, XcfaDeclarativeAction> concretize(
			final Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> trace, SolverFactory solverFactory) {
		List<XcfaDeclarativeState<?>> sbeStates = new ArrayList<>();
		List<XcfaDeclarativeAction> sbeActions = new ArrayList<>();

		sbeStates.add(trace.getState(0));
		for (int i = 0; i < trace.getActions().size(); ++i) {
			sbeStates.add(XcfaDeclarativeState.create(trace.getState(i+1).getCurrentLoc(), ExplState.top()));
			final XcfaEdge edge = XcfaEdge.of(trace.getAction(i).getSource(), trace.getAction(i).getTarget(), trace.getAction(i).getLabels());
			sbeActions.add(XcfaDeclarativeAction.create(edge));
			sbeStates.add(trace.getState(i+1));
		}
		Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> sbeTrace = Trace.of(sbeStates, sbeActions);
		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
				BoolExprs.True(), solverFactory.createItpSolver());
		final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
		checkArgument(status.isFeasible(), "Infeasible trace.");
		final Trace<Valuation, ? extends Action> valuations = status.asFeasible().getValuations();

		assert valuations.getStates().size() == sbeTrace.getStates().size();

		final List<XcfaDeclarativeState<ExplState>> cfaStates = new ArrayList<>();
		for (int i = 0; i < sbeTrace.getStates().size(); ++i) {
			cfaStates.add(XcfaDeclarativeState.create(sbeTrace.getState(i).getCurrentLoc(), ExplState.of(valuations.getState(i))));
		}

		return Trace.of(cfaStates, sbeTrace.getActions());
	}

}
