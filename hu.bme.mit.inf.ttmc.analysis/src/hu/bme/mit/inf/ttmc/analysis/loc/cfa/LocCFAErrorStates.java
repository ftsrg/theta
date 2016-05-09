package hu.bme.mit.inf.ttmc.analysis.loc.cfa;

import hu.bme.mit.inf.ttmc.analysis.ErrorStates;
import hu.bme.mit.inf.ttmc.analysis.loc.LocState;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;

public class LocCFAErrorStates implements ErrorStates<LocState<CFALoc>> {

	private final CFA automaton;

	public LocCFAErrorStates(final CFA automaton) {
		this.automaton = automaton;
	}

	@Override
	public boolean isError(final LocState<CFALoc> state) {
		return automaton.getErrorLoc().equals(state);
	}

}
