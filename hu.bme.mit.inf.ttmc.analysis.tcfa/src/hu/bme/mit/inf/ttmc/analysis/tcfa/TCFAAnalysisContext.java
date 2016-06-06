package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAAnalysisContext implements AnalysisContext<TCFAState<?>, TCFALoc, TCFAEdge, TCFALoc> {

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
	public Collection<? extends TCFAEdge> getTransitions(final TCFAState<?> state) {
		return state.getLoc().getOutEdges();
	}

	@Override
	public TCFALoc getTarget() {
		return targetLoc;
	}

}
