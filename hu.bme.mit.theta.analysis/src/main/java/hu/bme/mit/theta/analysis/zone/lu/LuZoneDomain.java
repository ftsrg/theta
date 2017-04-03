package hu.bme.mit.theta.analysis.zone.lu;

import hu.bme.mit.theta.analysis.Domain;

public final class LuZoneDomain implements Domain<LuZoneState> {
	private static final LuZoneDomain INSTANCE = new LuZoneDomain();

	private LuZoneDomain() {
	}

	public static LuZoneDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final LuZoneState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final LuZoneState state) {
		return state.isBottom();
	}

	@Override
	public boolean isLeq(final LuZoneState state1, final LuZoneState state2) {
		return state1.isLeq(state2);
	}

}
