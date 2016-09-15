package hu.bme.mit.theta.analysis.tcfa.lawi;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.composite.CompositeDomain;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplDomain;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaDomain;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaLawiDomain implements Domain<TcfaLawiState> {

	private static final TcfaLawiDomain INSTANCE = new TcfaLawiDomain();

	private final TcfaDomain<CompositeState<ZoneState, ExplState>> domain;

	private TcfaLawiDomain() {
		final ZoneDomain zoneDomain = ZoneDomain.getInstance();
		final ExplDomain explDomain = ExplDomain.getInstance();
		final CompositeDomain<ZoneState, ExplState> compositeDomain = CompositeDomain.create(zoneDomain, explDomain);
		domain = TcfaDomain.create(compositeDomain);
	}

	public static TcfaLawiDomain getInstance() {
		return INSTANCE;
	}

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

	@Override
	public TcfaLawiState join(final TcfaLawiState state1, final TcfaLawiState state2) {
		final TcfaState<CompositeState<ZoneState, ExplState>> state = domain.join(state1.getState(), state2.getState());
		return TcfaLawiState.create(state);
	}

}
