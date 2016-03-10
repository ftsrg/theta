package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class DoStmtImpl extends AbstractStmt implements DoStmt {

	private final static int HASHSEED = 599;
	private volatile int hashCode = 0;
	
	private final Stmt doStmt;
	private final Expr<? extends BoolType> cond;
	
	public DoStmtImpl(final Stmt doStmt, final Expr<? extends BoolType> cond) {
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
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + doStmt.hashCode();
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
			final DoStmtImpl that = (DoStmtImpl) obj;
			return this.doStmt.equals(that.doStmt) && this.cond.equals(that.cond);
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
