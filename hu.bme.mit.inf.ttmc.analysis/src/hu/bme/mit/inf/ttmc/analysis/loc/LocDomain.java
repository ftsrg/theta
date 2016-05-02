package hu.bme.mit.inf.ttmc.analysis.loc;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;

public class LocDomain<L extends Loc<L, ?>> implements Domain<LocState<L>> {

	private LocDomain() {
	}

	public static <L extends Loc<L, ?>> LocDomain<L> create() {
		return new LocDomain<>();
	}

	@Override
	public LocState<L> join(final LocState<L> state1, final LocState<L> state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final LocState<L> state1, final LocState<L> state2) {
		return state1.equals(state2);
	}

}
