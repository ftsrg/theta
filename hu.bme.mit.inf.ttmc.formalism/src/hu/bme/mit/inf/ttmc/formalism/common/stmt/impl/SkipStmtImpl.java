package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.SkipStmt;

final class SkipStmtImpl extends AbstractStmt implements SkipStmt {

	private final static int HASH_CODE = 1310147;

	SkipStmtImpl() {
	}

	@Override
	public int hashCode() {
		return HASH_CODE;
	}

	@Override
	public boolean equals(final Object obj) {
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
