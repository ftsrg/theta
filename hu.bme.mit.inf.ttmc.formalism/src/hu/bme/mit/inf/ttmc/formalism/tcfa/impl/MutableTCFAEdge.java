package hu.bme.mit.inf.ttmc.formalism.tcfa.impl;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;

final class MutableTCFAEdge implements TCFAEdge {

	MutableTCFALoc source;
	MutableTCFALoc target;

	MutableTCFAEdge(final MutableTCFALoc source, final MutableTCFALoc target) {
		this.source = source;
		this.target = target;
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
