package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class MutableTCFALoc implements TCFALoc {

	final Collection<MutableTCFAEdge> inEdges;
	final Collection<MutableTCFAEdge> outEdges;

	MutableTCFALoc() {
		inEdges = new LinkedList<>();
		outEdges = new LinkedList<>();
	}

	@Override
	public boolean isUrgent() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Expr<? extends BoolType> getInvar() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends TCFAEdge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	@Override
	public Collection<? extends TCFAEdge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

}
