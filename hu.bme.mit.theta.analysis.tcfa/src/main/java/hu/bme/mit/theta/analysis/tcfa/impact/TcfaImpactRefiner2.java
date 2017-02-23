package hu.bme.mit.theta.analysis.tcfa.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactRefiner;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.zone.TcfaInterpolator;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.ItpZoneState;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaImpactRefiner2
		implements ImpactRefiner<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> {

	private final TcfaInterpolator interpolator;

	private TcfaImpactRefiner2(final TCFA tcfa) {
		checkNotNull(tcfa);
		interpolator = TcfaInterpolator.create(ZonePrec.create(tcfa.getClockVars()));
	}

	public static TcfaImpactRefiner2 create(final TCFA tcfa) {
		return new TcfaImpactRefiner2(tcfa);
	}

	@Override
	public RefinementResult<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> refine(
			final Trace<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> cex) {
		final List<TcfaAction> actions = cex.getActions();

		final List<ZoneState> interpolants = interpolator.getInterpolant(actions);
		final List<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>> refinedStates = new ArrayList<>();
		for (int i = 0; i < interpolants.size(); i++) {
			final LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge> state = cex.getState(i);

			final ItpZoneState itpState = state.getState()._2();
			final ZoneState oldInterpolant = itpState.getInterpolant();
			final ZoneState interpolant = interpolants.get(i);
			final ZoneState newInterpolant = ZoneState.intersection(oldInterpolant, interpolant);
			final ItpZoneState newItpState = itpState.withInterpolant(newInterpolant);

			final LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge> refinedState = state
					.withState(state.getState().with2(newItpState));
			refinedStates.add(refinedState);
		}

		final Trace<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> refinedTrace = Trace
				.of(refinedStates, actions);

		return RefinementResult.succesful(refinedTrace);
	}

}
