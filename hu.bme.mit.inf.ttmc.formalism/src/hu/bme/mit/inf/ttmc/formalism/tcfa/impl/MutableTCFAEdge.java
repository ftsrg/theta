package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.LinkedList;
import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class MutableTCFAEdge implements TCFAEdge {

	MutableTCFALoc source;
	MutableTCFALoc target;

	private final List<Stmt> stmts;

	MutableTCFAEdge(final MutableTCFALoc source, final MutableTCFALoc target) {
		this.source = source;
		this.target = target;
		stmts = new LinkedList<>();
	}

	@Override
	public TCFALoc getSource() {
		return source;
	}

	@Override
	public TCFALoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

}
