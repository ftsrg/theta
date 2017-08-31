package hu.bme.mit.theta.analysis.zone.act;

import hu.bme.mit.theta.analysis.Domain;

public final class ActZoneDomain implements Domain<ActZoneState> {

	private ActZoneDomain() {
	}

	private static class LazyHolder {
		static final ActZoneDomain INSTANCE = new ActZoneDomain();
	}

	public static ActZoneDomain getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public boolean isTop(final ActZoneState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final ActZoneState state) {
		return state.isBottom();
	}

	@Override
	public boolean isLeq(final ActZoneState state1, final ActZoneState state2) {
		return state1.isLeq(state2);
	}

}
