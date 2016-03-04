package hu.bme.mit.inf.ttmc.program.tcfa.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFALoc;

public class MutableTCFALocImpl implements TCFALoc {

	private MutableTCFAImpl tcfa;
	private Expr<? extends BoolType> invar;
	private boolean urgent;
	
	private final Collection<MutableTCFAEdgeImpl> inEdges;
	private final Collection<MutableTCFAEdgeImpl> outEdges;
	
	
	MutableTCFALocImpl(final MutableTCFAImpl tcfa, final Expr<? extends BoolType> invar, final boolean urgent) {
		this.tcfa = tcfa;
		this.invar = invar;
		this.urgent = urgent;
		inEdges = new HashSet<>();
		outEdges = new HashSet<>();
	}
	
	////
	
	@Override
	public MutableTCFAImpl getTCFA() {
		return tcfa;
	}
	
	void setTCFA(MutableTCFAImpl tcfa) {
		this.tcfa = tcfa;
	}

	////

	@Override
	public boolean isUrgent() {
		return urgent;
	}
	
	public void setUrgent(boolean urgent) {
		this.urgent = urgent;
	}
	
	////

	@Override
	public Expr<? extends BoolType> getInvar() {
		return invar;
	}
	
	public void setInvar(Expr<? extends BoolType> invar) {
		this.invar = invar;
	}
	
	////

	@Override
	public Collection<MutableTCFAEdgeImpl> getInEdges() {	
		return Collections.unmodifiableCollection(inEdges);
	}
	
	void addInEdge(final MutableTCFAEdgeImpl edge) {
		inEdges.add(edge);
	}
	
	void removeInEdge(final MutableTCFAEdgeImpl edge) {
		inEdges.remove(edge);
	}
	
	////

	@Override
	public Collection<MutableTCFAEdgeImpl> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}
	
	void addOutEdge(final MutableTCFAEdgeImpl edge) {
		outEdges.add(edge);
	}
	
	void removeOutEdge(final MutableTCFAEdgeImpl edge) {
		outEdges.remove(edge);
	}
	
}
