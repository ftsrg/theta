package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class MutableTCFAEdge implements TCFAEdge {

	final MutableTCFALoc source;
	final MutableTCFALoc target;

	private final List<Stmt> stmts;

	MutableTCFAEdge(final MutableTCFALoc source, final MutableTCFALoc target, final List<? extends Stmt> stmts) {
		this.source = source;
		this.target = target;
		this.stmts = ImmutableList.copyOf(stmts);
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
