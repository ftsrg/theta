package hu.bme.mit.inf.ttmc.analysis.zone;

import hu.bme.mit.inf.ttmc.analysis.Domain;

public final class ZoneDomain implements Domain<ZoneState> {

	private static final ZoneDomain INSTANCE = new ZoneDomain();

	private ZoneDomain() {
	}

	public static ZoneDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final ZoneState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final ZoneState state) {
		return state.isBottom();
	}

	@Override
	public boolean isLeq(final ZoneState state1, final ZoneState state2) {
		return state1.isLeq(state2);
	}

	@Override
	public ZoneState join(final ZoneState state1, final ZoneState state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
