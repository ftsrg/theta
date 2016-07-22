package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.State;

final class TCFADomain<S extends State> implements Domain<TCFAState<S>> {

	private final Domain<S> domain;

	TCFADomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	@Override
	public boolean isTop(final TCFAState<S> state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final TCFAState<S> state) {
		return domain.isBottom(state.getState());
	}

	@Override
	public boolean isLeq(final TCFAState<S> state1, final TCFAState<S> state2) {
		return state1.getLoc().equals(state2.getLoc()) && domain.isLeq(state1.getState(), state2.getState());
	}

	@Override
	public TCFAState<S> join(final TCFAState<S> state1, final TCFAState<S> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
