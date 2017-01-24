package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.Domain;

public final class ExplDomain implements Domain<ExplState> {

	private static final ExplDomain INSTANCE;

	static {
		INSTANCE = new ExplDomain();
	}

	private ExplDomain() {
	}

	public static ExplDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final ExplState state) {
		return state.getDecls().isEmpty();
	}

	@Override
	public boolean isBottom(final ExplState state) {
		return false;
	}

	@Override
	public boolean isLeq(final ExplState state1, final ExplState state2) {
		return state1.isLeq(state2);
	}

}
