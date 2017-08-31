package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

public final class LocDomain<S extends State> implements Domain<LocState<S>> {

	private final Domain<S> domain;

	private LocDomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	public static <S extends State> LocDomain<S> create(final Domain<S> domain) {
		return new LocDomain<>(domain);
	}

	@Override
	public boolean isTop(final LocState<S> state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final LocState<S> state) {
		return domain.isBottom(state.getState());
	}

	@Override
	public boolean isLeq(final LocState<S> state1, final LocState<S> state2) {
		return state1.getLoc().equals(state2.getLoc()) && domain.isLeq(state1.getState(), state2.getState());
	}

}
