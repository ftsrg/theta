package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TcfaLoc;

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
