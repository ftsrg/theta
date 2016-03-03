package hu.bme.mit.inf.ttmc.program.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFALoc;

public class MutableTCFALocImpl implements TCFALoc {

	private MutableTCFAImpl tcfa;
	
	MutableTCFALocImpl(final MutableTCFAImpl tcfa) {
		this.tcfa = tcfa;
	}
	
	////
	
	@Override
	public MutableTCFAImpl getTCFA() {
		return tcfa;
	}
	
	void unsetTCFA() {
		checkArgument(!tcfa.getLocs().contains(this));
		tcfa = null;
	}

	////

	@Override
	public boolean isUrgent() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	public boolean setUrgent(boolean urgent) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	////

	@Override
	public Expr<? extends BoolType> getInvar() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	public void setInvar(Expr<? extends BoolType> expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	////

	@Override
	public Collection<MutableTCFAEdgeImpl> getInEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	void addInEdge(final MutableTCFAEdgeImpl edge) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	void removeInEdge(final MutableTCFAEdgeImpl edge) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	////

	@Override
	public Collection<MutableTCFAEdgeImpl> getOutEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	void addOutEdge(final MutableTCFAEdgeImpl edge) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	void removeOutEdge(final MutableTCFAEdgeImpl edge) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
}
