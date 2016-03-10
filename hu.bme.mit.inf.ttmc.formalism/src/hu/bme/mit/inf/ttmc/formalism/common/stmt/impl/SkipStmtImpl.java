package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.SkipStmt;

public class SkipStmtImpl extends AbstractStmt implements SkipStmt {
	
	private final static int HASHCODE = 1310147;
	
	@Override
	public int hashCode() {
		return HASHCODE;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			return true;
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return "Skip";
	}
	
}
