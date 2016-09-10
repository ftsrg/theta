package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

final class TcfaDomain<S extends State> implements Domain<TcfaState<S>> {

	private final Domain<S> domain;

	TcfaDomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	@Override
	public boolean isTop(final TcfaState<S> state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final TcfaState<S> state) {
		return domain.isBottom(state.getState());
	}

	@Override
	public boolean isLeq(final TcfaState<S> state1, final TcfaState<S> state2) {
		return state1.getLoc().equals(state2.getLoc()) && domain.isLeq(state1.getState(), state2.getState());
	}

	@Override
	public TcfaState<S> join(final TcfaState<S> state1, final TcfaState<S> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
