package hu.bme.mit.inf.ttmc.analysis.tcfa.expl;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

public class TCFAExplInitFunction implements InitFunction<ExplState, ExplPrecision, TCFALoc> {

	@Override
	public Collection<ExplState> getInitStates(final ExplPrecision precision, final TCFALoc init) {
		return Collections.singleton(ExplState.create(Valuation.builder().build()));
	}

}
