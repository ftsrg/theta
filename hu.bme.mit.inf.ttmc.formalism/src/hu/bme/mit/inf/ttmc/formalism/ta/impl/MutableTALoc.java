package hu.bme.mit.inf.ttmc.formalism.ta.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.formalism.ta.TAEdge;
import hu.bme.mit.inf.ttmc.formalism.ta.TALoc;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

final class MutableTALoc implements TALoc {

	final Collection<TAEdge> inEdges;
	final Collection<TAEdge> outEdges;

	private final ClockConstr invar;

	MutableTALoc(final ClockConstr invar) {
		this.invar = invar;
		inEdges = new ArrayList<>();
		outEdges = new ArrayList<>();
	}

	@Override
	public Collection<? extends TAEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<? extends TAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	@Override
	public ClockConstr getInvar() {
		return invar;
	}

}
