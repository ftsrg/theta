package hu.bme.mit.inf.ttmc.analysis.arg;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.State;

public class ArgDomain<S extends State> implements Domain<ArgState<S>> {

	private final Domain<S> domain;

	private ArgDomain(final Domain<S> domain) {
		this.domain = checkNotNull(domain);
	}

	public static <S extends State> ArgDomain<S> create(final Domain<S> domain) {
		return new ArgDomain<>(domain);
	}

	@Override
	public ArgState<S> join(final ArgState<S> state1, final ArgState<S> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public boolean isLeq(final ArgState<S> state1, final ArgState<S> state2) {
		return domain.isLeq(state1.getState(), state2.getState());
	}

}
