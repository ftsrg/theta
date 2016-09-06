package hu.bme.mit.inf.theta.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.common.stmt.IfStmt;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;

final class IfStmtImpl extends AbstractStmt implements IfStmt {

	private static final int HASH_SEED = 829;
	private volatile int hashCode = 0;

	private final Expr<? extends BoolType> cond;
	private final Stmt then;

	IfStmtImpl(final Expr<? extends BoolType> cond, final Stmt then) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
	}

	@Override
	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	@Override
	public Stmt getThen() {
		return then;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + cond.hashCode();
			result = 31 * result + then.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IfStmt) {
			final IfStmt that = (IfStmt) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("If");
		sb.append("(");
		sb.append(cond.toString());
		sb.append(", ");
		sb.append(then.toString());
		sb.append(")");
		return sb.toString();
	}

}
