package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

final class TcfaLawiInitFunction implements InitFunction<TcfaLawiState, UnitPrec> {

	private final InitFunction<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, UnitPrec> initFunction;

	private TcfaLawiInitFunction(
			final InitFunction<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, UnitPrec> initFunction) {
		this.initFunction = checkNotNull(initFunction);
	}

	public static TcfaLawiInitFunction create(
			final InitFunction<LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge>, UnitPrec> initFunction) {
		return new TcfaLawiInitFunction(initFunction);
	}

	@Override
	public Collection<? extends TcfaLawiState> getInitStates(final UnitPrec prec) {
		return initFunction.getInitStates(prec).stream().map(TcfaLawiState::create).collect(toList());
	}

}
