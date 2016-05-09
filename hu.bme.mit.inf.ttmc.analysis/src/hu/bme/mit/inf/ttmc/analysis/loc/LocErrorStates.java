package hu.bme.mit.inf.ttmc.analysis.loc;

import hu.bme.mit.inf.ttmc.analysis.ErrorStates;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Automaton;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;

public class LocErrorStates<L extends Loc<L, ?>> implements ErrorStates<LocState<L>> {

	private final Automaton<L, ?> automaton;

	public LocErrorStates(final Automaton<L, ?> automaton) {
		this.automaton = automaton;
	}

	@Override
	public boolean isError(final LocState<L> state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

}
