package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLawiDomain implements Domain<TcfaLawiState> {

	private final Domain<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>> domain;

	private TcfaLawiDomain(final Domain<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>> domain) {
		this.domain = checkNotNull(domain);
	}

	public static TcfaLawiDomain create(
			final Domain<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>> domain) {
		return new TcfaLawiDomain(domain);
	}

	////

	@Override
	public boolean isTop(final TcfaLawiState state) {
		return domain.isTop(state.getState());
	}

	@Override
	public boolean isBottom(final TcfaLawiState state) {
		return domain.isBottom(state.getState());
	}

	@Override
	public boolean isLeq(final TcfaLawiState state1, final TcfaLawiState state2) {
		return domain.isLeq(state1.getState(), state2.getState());

	}

}
