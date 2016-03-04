package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public class MutableCFAEdgeImpl implements CFAEdge {

	private MutableCFAImpl cfa;
	private MutableCFALocImpl source;
	private MutableCFALocImpl target;
	private final List<Stmt> stmts;
	
	MutableCFAEdgeImpl(final MutableCFAImpl cfa, final MutableCFALocImpl source, final MutableCFALocImpl target) {
		this.cfa = cfa;
		this.source = source;
		this.target = target;
		stmts = new ArrayList<>();
	}

	////

	@Override
	public CFA getCFA() {
		return cfa;
	}
	
	void setCFA(final MutableCFAImpl cfa) {
		this.cfa = cfa;
	}

	////

	@Override
	public MutableCFALocImpl getSource() {
		return source;
	}

	@Override
	public MutableCFALocImpl getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	////

}
