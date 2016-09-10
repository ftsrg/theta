package hu.bme.mit.theta.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.theta.formalism.common.stmt.WhileStmt;

final class WhileStmtImpl extends AbstractStmt implements WhileStmt {

	private final static int HASH_SEED = 631;
	private volatile int hashCode = 0;

	private final Expr<? extends BoolType> cond;
	private final Stmt doStmt;

	WhileStmtImpl(final Expr<? extends BoolType> cond, final Stmt doStmt) {
		this.cond = checkNotNull(cond);
		this.doStmt = checkNotNull(doStmt);
	}

	@Override
	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	@Override
	public Stmt getDo() {
		return doStmt;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + cond.hashCode();
			result = 31 * result + doStmt.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof WhileStmt) {
			final WhileStmt that = (WhileStmt) obj;
			return this.getCond().equals(that.getCond()) && this.getDo().equals(that.getDo());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("While");
		sb.append("(");
		sb.append(cond.toString());
		sb.append(", ");
		sb.append(doStmt.toString());
		sb.append(")");
		return sb.toString();
	}
}
