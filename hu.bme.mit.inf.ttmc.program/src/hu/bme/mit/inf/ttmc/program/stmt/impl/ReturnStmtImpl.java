package hu.bme.mit.inf.ttmc.program.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.stmt.ReturnStmt;

public class ReturnStmtImpl<ReturnType extends Type> implements ReturnStmt<ReturnType> {

	private final static int HASHSEED = 1009;
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
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + expr.hashCode();
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
			final ReturnStmtImpl<?> that = (ReturnStmtImpl<?>) obj;
			return this.expr.equals(that.expr);
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
