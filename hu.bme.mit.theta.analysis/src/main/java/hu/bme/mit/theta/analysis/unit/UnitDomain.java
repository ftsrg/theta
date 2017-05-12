package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;

final class UnitDomain implements Domain<UnitState> {

	private static final UnitDomain INSTANCE = new UnitDomain();

	private UnitDomain() {
	}

	public static UnitDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final UnitState state) {
		checkNotNull(state);
		return true;
	}

	@Override
	public boolean isBottom(final UnitState state) {
		checkNotNull(state);
		return false;
	}

	@Override
	public boolean isLeq(final UnitState state1, final UnitState state2) {
		checkNotNull(state1);
		checkNotNull(state2);
		return true;
	}

}
