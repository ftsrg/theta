package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAAnalysisContext implements AnalysisContext<TCFAState<?>, TCFALoc, TCFATrans, TCFALoc> {

	private final TCFALoc initLoc;
	private final TCFALoc targetLoc;

	public TCFAAnalysisContext(final TCFALoc initLoc, final TCFALoc targetLoc) {
		this.initLoc = checkNotNull(initLoc);
		this.targetLoc = checkNotNull(targetLoc);
	}

	@Override
	public TCFALoc getInitialization() {
		return initLoc;
	}

	@Override
	public Collection<TCFATrans> getTransitions(final TCFAState<?> state) {
		final Collection<TCFATrans> tcfaTrans = new ArrayList<>();
		final TCFALoc loc = state.getLoc();

		for (final TCFAEdge outEdge : loc.getOutEdges()) {
			tcfaTrans.add(TCFATrans.discrete(outEdge));
		}

		if (!loc.isUrgent()) {
			tcfaTrans.add(TCFATrans.delay());
		}

		return tcfaTrans;
	}

	@Override
	public TCFALoc getTarget() {
		return targetLoc;
	}

}
