package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.common.Valuation;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLawiInitFunction implements InitFunction<TcfaLawiState, NullPrecision> {

	private final TcfaLoc initLoc;

	TcfaLawiInitFunction(final TCFA tcfa) {
		checkNotNull(tcfa);
		initLoc = tcfa.getInitLoc();
	}

	@Override
	public Collection<? extends TcfaLawiState> getInitStates(final NullPrecision precision) {
		final ZoneState zoneState = ZoneState.top(Collections.emptySet());
		final ExplState explState = ExplState.create(Valuation.builder().build());
		final CompositeState<ZoneState, ExplState> compositeState = CompositeState.create(zoneState, explState);
		final TcfaState<CompositeState<ZoneState, ExplState>> tcfaState = TcfaState.create(initLoc, compositeState);
		final TcfaLawiState lawiState = TcfaLawiState.create(tcfaState);
		return Collections.singleton(lawiState);
	}

}
