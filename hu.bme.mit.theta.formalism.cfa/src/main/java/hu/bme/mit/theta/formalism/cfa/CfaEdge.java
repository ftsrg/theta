package hu.bme.mit.theta.formalism.cfa;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.common.Edge;

public final class CfaEdge implements Edge<CfaLoc, CfaEdge> {

	private final CfaLoc source;
	private final CfaLoc target;
	private final List<Stmt> stmts;

	CfaEdge(final CfaLoc source, final CfaLoc target) {
		this.source = source;
		this.target = target;
		stmts = new ArrayList<>();
	}

	////

	@Override
	public CfaLoc getSource() {
		return source;
	}

	@Override
	public CfaLoc getTarget() {
		return target;
	}

	public List<Stmt> getStmts() {
		return stmts;
	}

	////

}
