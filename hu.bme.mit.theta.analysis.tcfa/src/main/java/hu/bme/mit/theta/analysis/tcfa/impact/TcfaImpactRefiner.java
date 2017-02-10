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
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaImpactRefiner
		implements ImpactRefiner<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> {

	private final TcfaInterpolator interpolator;

	private TcfaImpactRefiner(final TCFA tcfa) {
		checkNotNull(tcfa);
		interpolator = TcfaInterpolator.create(ZonePrecision.create(tcfa.getClockVars()));
	}

	public static TcfaImpactRefiner create(final TCFA tcfa) {
		return new TcfaImpactRefiner(tcfa);
	}

	@Override
	public RefinementResult<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> refine(
			final Trace<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> cex) {
		final List<TcfaAction> actions = cex.getActions();

		final List<ZoneState> itpZones = interpolator.getInterpolant(actions);
		final List<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>> refinedStates = new ArrayList<>();
		for (int i = 0; i < itpZones.size(); i++) {
			final LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge> state = cex.getState(i);

			final ZoneState zone = state.getState()._2();
			final ZoneState itpZone = itpZones.get(i);
			final ZoneState refinedZone = ZoneState.intersection(zone, itpZone);

			final LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge> refinedState = state
					.withState(state.getState().with2(refinedZone));
			refinedStates.add(refinedState);
		}

		final Trace<LocState<Prod2State<ExplState, ZoneState>, TcfaLoc, TcfaEdge>, TcfaAction> refinedTrace = Trace
				.of(refinedStates, actions);
		return RefinementResult.succesful(refinedTrace);
	}

}
