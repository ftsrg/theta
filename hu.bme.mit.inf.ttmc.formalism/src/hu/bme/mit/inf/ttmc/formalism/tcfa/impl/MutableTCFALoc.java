package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class MutableTCFALoc implements TCFALoc {

	final Collection<MutableTCFAEdge> inEdges;
	final Collection<MutableTCFAEdge> outEdges;

	private final Collection<Expr<? extends BoolType>> invars;
	private boolean urgent;

	MutableTCFALoc() {
		inEdges = new LinkedList<>();
		outEdges = new LinkedList<>();
		invars = new LinkedList<>();
		urgent = false;
	}

	@Override
	public boolean isUrgent() {
		return urgent;
	}

	public void setUrgent(final boolean urgent) {
		this.urgent = urgent;
	}

	////

	@Override
	public Collection<Expr<? extends BoolType>> getInvars() {
		return invars;
	}

	////

	@Override
	public Collection<? extends TCFAEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<? extends TCFAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

}
