package hu.bme.mit.inf.theta.formalism.ta.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.theta.formalism.ta.TaEdge;
import hu.bme.mit.inf.theta.formalism.ta.TaLoc;
import hu.bme.mit.inf.theta.formalism.ta.constr.ClockConstr;

final class MutableTaLoc implements TaLoc {

	final Collection<TaEdge> inEdges;
	final Collection<TaEdge> outEdges;

	private final ClockConstr invar;

	MutableTaLoc(final ClockConstr invar) {
		this.invar = invar;
		inEdges = new ArrayList<>();
		outEdges = new ArrayList<>();
	}

	@Override
	public Collection<? extends TaEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<? extends TaEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	@Override
	public ClockConstr getInvar() {
		return invar;
	}

}
