package hu.bme.mit.inf.ttmc.analysis.arg;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.State;

public class ARGDomain<S extends State> implements Domain<ARGState<S>> {

	private final Domain<S> domain;

	private ARGDomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	public static <S extends State> ARGDomain<S> create(final Domain<S> domain) {
		return new ARGDomain<>(domain);
	}

	@Override
	public ARGState<S> join(final ARGState<S> state1, final ARGState<S> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public boolean isLeq(final ARGState<S> state1, final ARGState<S> state2) {
		return domain.isLeq(state1.getState(), state2.getState());
	}

}
