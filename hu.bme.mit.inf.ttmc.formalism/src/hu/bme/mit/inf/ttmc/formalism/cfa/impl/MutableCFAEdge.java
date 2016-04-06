package hu.bme.mit.inf.ttmc.formalism.cfa.impl;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

class MutableCFAEdge implements CFAEdge {

	private CFALoc source;
	private CFALoc target;
	private final List<Stmt> stmts;
	
	MutableCFAEdge(final MutableCFALoc source, final MutableCFALoc target) {
		this.source = source;
		this.target = target;
		stmts = new ArrayList<>();
	}

	////

	@Override
	public CFALoc getSource() {
		return source;
	}

	@Override
	public CFALoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	////

}
