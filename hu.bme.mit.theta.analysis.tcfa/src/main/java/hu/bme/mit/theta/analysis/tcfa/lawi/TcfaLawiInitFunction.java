package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.NullPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLawiInitFunction implements InitFunction<TcfaLawiState, NullPrecision> {

	private final InitFunction<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, NullPrecision> initFunction;

	private TcfaLawiInitFunction(
			final InitFunction<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, NullPrecision> initFunction) {
		this.initFunction = checkNotNull(initFunction);
	}

	public static TcfaLawiInitFunction create(
			final InitFunction<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, NullPrecision> initFunction) {
		return new TcfaLawiInitFunction(initFunction);
	}

	@Override
	public Collection<? extends TcfaLawiState> getInitStates(final NullPrecision precision) {
		return initFunction.getInitStates(precision).stream().map(TcfaLawiState::create).collect(toList());
	}

}
