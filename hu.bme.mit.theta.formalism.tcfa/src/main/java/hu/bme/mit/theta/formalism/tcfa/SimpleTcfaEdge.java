package hu.bme.mit.theta.formalism.tcfa;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.stmt.Stmt;

final class SimpleTcfaEdge implements TcfaEdge {

	final SimpleTcfaLoc source;
	final SimpleTcfaLoc target;

	private final List<Stmt> stmts;

	SimpleTcfaEdge(final SimpleTcfaLoc source, final SimpleTcfaLoc target, final List<? extends Stmt> stmts) {
		this.source = source;
		this.target = target;
		this.stmts = ImmutableList.copyOf(stmts);
	}

	@Override
	public TcfaLoc getSource() {
		return source;
	}

	@Override
	public TcfaLoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

}
