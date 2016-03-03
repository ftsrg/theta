package hu.bme.mit.inf.ttmc.program.tcfa.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFALoc;

final class TCFALocImpl implements TCFALoc {

	TCFALocImpl() {

	}

	////

	@Override
	public TCFA getTCFA() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends TCFAEdge> getOutEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
