package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.ReturnStmt;

public final class ReturnStmtImpl<ReturnType extends Type> implements ReturnStmt<ReturnType> {

	private static final int HASH_SEED = 1009;
	private volatile int hashCode = 0;

	private final Expr<? extends ReturnType> expr;

	public ReturnStmtImpl(final Expr<? extends ReturnType> expr) {
		this.expr = checkNotNull(expr);
	}

	@Override
	public Expr<? extends ReturnType> getExpr() {
		return expr;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + expr.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ReturnStmt<?>) {
			final ReturnStmt<?> that = (ReturnStmt<?>) obj;
			return this.getExpr().equals(that.getExpr());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Return");
		sb.append("(");
		sb.append(expr.toString());
		sb.append(")");
		return sb.toString();
	}

}
