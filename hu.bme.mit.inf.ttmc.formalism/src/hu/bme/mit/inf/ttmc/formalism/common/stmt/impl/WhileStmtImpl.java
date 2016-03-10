package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.WhileStmt;

public class WhileStmtImpl extends AbstractStmt implements WhileStmt {

	private final static int HASHSEED = 631;
	private volatile int hashCode = 0;
	
	private final Expr<? extends BoolType> cond;
	private final Stmt doStmt;
	
	public WhileStmtImpl(final Expr<? extends BoolType> cond, final Stmt doStmt) {
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
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + cond.hashCode();
			hashCode = 37 * hashCode + doStmt.hashCode();
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
			final WhileStmtImpl that = (WhileStmtImpl) obj;
			return this.cond.equals(that.cond) && this.doStmt.equals(that.doStmt);
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
