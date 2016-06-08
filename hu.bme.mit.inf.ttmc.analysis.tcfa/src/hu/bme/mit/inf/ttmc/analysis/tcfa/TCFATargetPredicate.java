package hu.bme.mit.inf.ttmc.analysis.tcfa;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFATargetPredicate implements TargetPredicate<TCFAState<? extends State>, TCFALoc> {

	@Override
	public boolean isTargetState(final TCFAState<? extends State> state, final TCFALoc targetLoc) {
		return state.getLoc().equals(targetLoc);
	}

}
