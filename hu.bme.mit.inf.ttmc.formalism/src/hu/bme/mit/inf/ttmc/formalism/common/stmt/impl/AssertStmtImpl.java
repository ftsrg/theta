package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;

public final class AssertStmtImpl extends AbstractStmt implements AssertStmt {

	private final static int HASHSEED = 733;
	private volatile int hashCode = 0;
	
	private final Expr<? extends BoolType> cond;

	public AssertStmtImpl(final Expr<? extends BoolType> cond) {
		this.cond = checkNotNull(cond);
	}
	
	@Override
	public Expr<? extends BoolType> getCond() {
		return cond;
	}
	
	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + cond.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final AssertStmtImpl that = (AssertStmtImpl) obj;
			return this.cond.equals(that.cond);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Assert");
		sb.append("(");
		sb.append(cond.toString());
		sb.append(")");
		return sb.toString();
	}
}
