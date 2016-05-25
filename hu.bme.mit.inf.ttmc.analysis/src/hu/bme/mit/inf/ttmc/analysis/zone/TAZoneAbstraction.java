package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.AutomatonAbstraction;
import hu.bme.mit.inf.ttmc.analysis.impl.NullPrecision;
import hu.bme.mit.inf.ttmc.formalism.ta.TAEdge;

public class TAZoneAbstraction implements AutomatonAbstraction<ZoneState, NullPrecision, TAEdge> {

	@Override
	public Collection<? extends ZoneState> getStartStates(final NullPrecision precision) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends ZoneState> getSuccStates(final ZoneState state, final NullPrecision precision) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends ZoneState> getSuccStatesForEdge(final ZoneState state, final NullPrecision precision,
			final TAEdge edge) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isTarget(final ZoneState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
