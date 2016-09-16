package hu.bme.mit.theta.core.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.IfElseStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;

final class IfElseStmtImpl extends AbstractStmt implements IfElseStmt {

	private static final int HASH_SEED = 661;
	private volatile int hashCode = 0;

	private final Expr<? extends BoolType> cond;
	private final Stmt then;
	private final Stmt elze;

	IfElseStmtImpl(final Expr<? extends BoolType> cond, final Stmt then, final Stmt elze) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
		this.elze = checkNotNull(elze);
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
	public Stmt getElse() {
		return elze;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + cond.hashCode();
			result = 31 * result + then.hashCode();
			result = 31 * result + elze.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IfElseStmt) {
			final IfElseStmt that = (IfElseStmt) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen())
					&& this.getElse().equals(that.getElse());
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
		sb.append(", ");
		sb.append(elze.toString());
		sb.append(")");
		return sb.toString();
	}
}
