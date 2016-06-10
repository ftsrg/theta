package hu.bme.mit.inf.ttmc.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.common.Unit;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;

public class TCFAExplInitFunction implements InitFunction<ExplState, ExplPrecision, Unit> {

	@Override
	public Collection<ExplState> getInitStates(final ExplPrecision precision, final Unit init) {
		checkNotNull(precision);
		checkNotNull(init);
		return Collections.singleton(ExplState.create(Valuation.builder().build()));
	}

}
