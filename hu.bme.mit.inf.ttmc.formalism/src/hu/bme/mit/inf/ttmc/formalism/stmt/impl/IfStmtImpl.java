package hu.bme.mit.inf.ttmc.formalism.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.Stmt;

public class IfStmtImpl extends AbstractStmt implements IfStmt {

	private final static int HASHSEED = 829;
	private volatile int hashCode = 0;
	
	private final Expr<? extends BoolType> cond;
	private final Stmt then;
	
	public IfStmtImpl(final Expr<? extends BoolType> cond, final Stmt then) {
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
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + cond.hashCode();
			hashCode = 37 * hashCode + then.hashCode();
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
			final IfStmtImpl that = (IfStmtImpl) obj;
			return this.cond.equals(that.cond) && this.then.equals(that.then);
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
