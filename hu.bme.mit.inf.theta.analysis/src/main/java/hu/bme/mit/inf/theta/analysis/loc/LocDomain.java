package hu.bme.mit.inf.theta.analysis.loc;

import hu.bme.mit.inf.theta.analysis.Domain;
import hu.bme.mit.inf.theta.formalism.common.automaton.Loc;

public class LocDomain<L extends Loc<L, ?>> implements Domain<LocState<L>> {

	private LocDomain() {
	}

	public static <L extends Loc<L, ?>> LocDomain<L> create() {
		return new LocDomain<>();
	}

	@Override
	public boolean isTop(final LocState<L> state) {
		return false;
	}

	@Override
	public boolean isBottom(final LocState<L> state) {
		return false;
	}

	@Override
	public boolean isLeq(final LocState<L> state1, final LocState<L> state2) {
		return state1.equals(state2);
	}

	@Override
	public LocState<L> join(final LocState<L> state1, final LocState<L> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
