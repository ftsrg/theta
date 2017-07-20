package hu.bme.mit.theta.analysis.xta.algorithm.lazy;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.algorithm.lazy.LazyXtaStatistics.Builder;
import hu.bme.mit.theta.analysis.zone.act.ActZoneState;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class ActStrategy implements LazyXtaChecker.AlgorithmStrategy<ActZoneState> {

	private ActStrategy(final XtaSystem system) {
		checkNotNull(system);
		// TODO Auto-generated constructor stub
	}

	public static ActStrategy create(final XtaSystem system) {
		return new ActStrategy(system);
	}

	@Override
	public Analysis<ActZoneState, XtaAction, UnitPrec> getAnalysis() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean covers(final ArgNode<XtaState<ActZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ActZoneState>, XtaAction> coveringNode) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean mightCover(final ArgNode<XtaState<ActZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ActZoneState>, XtaAction> coveringNode) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean shouldRefine(final ArgNode<XtaState<ActZoneState>, XtaAction> node) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> forceCover(
			final ArgNode<XtaState<ActZoneState>, XtaAction> nodeToCover,
			final ArgNode<XtaState<ActZoneState>, XtaAction> coveringNode, final Builder statistics) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<ArgNode<XtaState<ActZoneState>, XtaAction>> refine(
			final ArgNode<XtaState<ActZoneState>, XtaAction> node, final Builder statistics) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public void resetState(final ArgNode<XtaState<ActZoneState>, XtaAction> node) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
