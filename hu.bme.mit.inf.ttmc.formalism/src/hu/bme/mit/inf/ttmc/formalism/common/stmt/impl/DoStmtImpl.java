package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

final class DoStmtImpl extends AbstractStmt implements DoStmt {

	private static final int HASH_SEED = 599;
	private volatile int hashCode = 0;

	private final Stmt doStmt;
	private final Expr<? extends BoolType> cond;

	DoStmtImpl(final Stmt doStmt, final Expr<? extends BoolType> cond) {
		this.doStmt = checkNotNull(doStmt);
		this.cond = checkNotNull(cond);
	}

	@Override
	public Stmt getDo() {
		return doStmt;
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
			result = 31 * result + doStmt.hashCode();
			result = 31 * result + cond.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DoStmt) {
			final DoStmt that = (DoStmt) obj;
			return this.getDo().equals(that.getDo()) && this.getCond().equals(that.getCond());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Do");
		sb.append("(");
		sb.append(doStmt.toString());
		sb.append(", ");
		sb.append(cond.toString());
		sb.append(")");
		return sb.toString();
	}
}
