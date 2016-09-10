package hu.bme.mit.theta.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.stmt.AssumeStmt;

final class AssumeStmtImpl extends AbstractStmt implements AssumeStmt {

	private static final int HASH_SEED = 547;
	private volatile int hashCode = 0;

	private final Expr<? extends BoolType> cond;

	AssumeStmtImpl(final Expr<? extends BoolType> cond) {
		this.cond = checkNotNull(cond);
	}

	@Override
	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + cond.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AssumeStmt) {
			final AssumeStmt that = (AssumeStmt) obj;
			return this.getCond().equals(that.getCond());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Assume");
		sb.append("(");
		sb.append(cond.toString());
		sb.append(")");
		return sb.toString();
	}
}
