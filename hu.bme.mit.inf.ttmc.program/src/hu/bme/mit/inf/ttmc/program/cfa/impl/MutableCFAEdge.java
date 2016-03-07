package hu.bme.mit.inf.ttmc.program.cfa.impl;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public class MutableCFAEdge implements CFAEdge {

	private MutableCFALoc source;
	private MutableCFALoc target;
	private final List<Stmt> stmts;
	
	MutableCFAEdge(final MutableCFALoc source, final MutableCFALoc target) {
		this.source = source;
		this.target = target;
		stmts = new ArrayList<>();
	}

	////

	@Override
	public MutableCFALoc getSource() {
		return source;
	}

	@Override
	public MutableCFALoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	////

}
