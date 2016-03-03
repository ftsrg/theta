package hu.bme.mit.inf.ttmc.program.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;

import hu.bme.mit.inf.ttmc.program.stmt.Stmt;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFAEdge;

public class MutableTCFAEdgeImpl implements TCFAEdge {

	private MutableTCFAImpl tcfa;
	
	MutableTCFAEdgeImpl(final MutableTCFAImpl tcfa, final MutableTCFALocImpl source, final MutableTCFALocImpl target) {

	}

	////

	@Override
	public TCFA getTCFA() {
		return tcfa;
	}
	
	void unsetTCFA() {
		checkArgument(!tcfa.getEdges().contains(this));
		tcfa = null;
	}

	////

	@Override
	public MutableTCFALocImpl getSource() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public void setSource(MutableTCFALocImpl source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	@Override
	public MutableTCFALocImpl getTarget() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public void setTarget(final MutableTCFALocImpl target) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	@Override
	public List<Stmt> getStmts() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

}
