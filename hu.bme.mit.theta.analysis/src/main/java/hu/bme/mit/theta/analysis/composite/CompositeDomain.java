package hu.bme.mit.theta.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

class CompositeDomain<S1 extends State, S2 extends State> implements Domain<CompositeState<S1, S2>> {

	private final Domain<S1> domain1;
	private final Domain<S2> domain2;

	CompositeDomain(final Domain<S1> domain1, final Domain<S2> domain2) {
		this.domain1 = checkNotNull(domain1);
		this.domain2 = checkNotNull(domain2);
	}

	@Override
	public boolean isTop(final CompositeState<S1, S2> state) {
		return domain1.isTop(state._1()) && domain2.isTop(state._2());
	}

	@Override
	public boolean isBottom(final CompositeState<S1, S2> state) {
		return domain1.isBottom(state._1()) || domain2.isBottom(state._2());
	}

	@Override
	public boolean isLeq(final CompositeState<S1, S2> state1, final CompositeState<S1, S2> state2) {
		return domain1.isLeq(state1._1(), state2._1()) && domain2.isLeq(state1._2(), state2._2());
	}

	@Override
	public CompositeState<S1, S2> join(final CompositeState<S1, S2> state1, final CompositeState<S1, S2> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
