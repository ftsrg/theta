package hu.bme.mit.theta.analysis.zone.itp;

import hu.bme.mit.theta.analysis.Domain;

public final class ItpZoneDomain implements Domain<ItpZoneState> {

	private static final ItpZoneDomain INSTANCE = new ItpZoneDomain();

	private ItpZoneDomain() {
	}

	public static ItpZoneDomain getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public boolean isTop(final ItpZoneState state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isBottom(final ItpZoneState state) {
		return state.getInterpolant().isBottom();
	}

	@Override
	public boolean isLeq(final ItpZoneState state1, final ItpZoneState state2) {
		return state1.isLeq(state2);
	}

}
