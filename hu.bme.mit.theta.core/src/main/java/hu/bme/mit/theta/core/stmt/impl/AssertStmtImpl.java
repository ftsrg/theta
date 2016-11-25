package hu.bme.mit.theta.core.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssertStmt;
import hu.bme.mit.theta.core.type.BoolType;

final class AssertStmtImpl extends AbstractStmt implements AssertStmt {

	private static final int HASH_SEED = 733;
	private volatile int hashCode = 0;

	private final Expr<? extends BoolType> cond;

	AssertStmtImpl(final Expr<? extends BoolType> cond) {
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
		} else if (obj instanceof AssertStmt) {
			final AssertStmt that = (AssertStmt) obj;
			return this.getCond().equals(that.getCond());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Assert").add(cond).toString();
	}
}
