package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class SkipStmt implements Stmt {

	private final static int HASH_CODE = 1310147;

	SkipStmt() {
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
