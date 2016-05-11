package hu.bme.mit.inf.ttmc.analysis.loc;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitStates;
import hu.bme.mit.inf.ttmc.analysis.impl.NullPrecision;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Automaton;
import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;

public class LocInitStates<L extends Loc<L, ?>> implements InitStates<LocState<L>, NullPrecision> {

	private final Automaton<L, ?> automaton;

	public LocInitStates(final Automaton<L, ?> automaton) {
		this.automaton = automaton;
	}

	@Override
	public Collection<? extends LocState<L>> get(final NullPrecision precision) {
		return Collections.singleton(LocState.create(automaton.getInitLoc()));
	}

}
