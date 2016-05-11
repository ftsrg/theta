package hu.bme.mit.inf.ttmc.analysis.loc;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;

public class CFALocAbstraction extends LocAbstraction<CFALoc, CFAEdge> {

	private final CFA automaton;

	public CFALocAbstraction(final CFA automaton) {
		super(automaton);
		this.automaton = automaton;
	}

	@Override
	public boolean isTarget(final LocState<CFALoc> state) {
		return automaton.getErrorLoc().equals(state);
	}

}
