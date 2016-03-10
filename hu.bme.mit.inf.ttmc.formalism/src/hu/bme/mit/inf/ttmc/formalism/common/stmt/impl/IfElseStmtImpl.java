package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class IfElseStmtImpl extends AbstractStmt implements IfElseStmt {

	private final static int HASHSEED = 661;
	private volatile int hashCode = 0;
	
	private final Expr<? extends BoolType> cond;
	private final Stmt then;
	private final Stmt elze;
	
	public IfElseStmtImpl(final Expr<? extends BoolType> cond, final Stmt then,  final Stmt elze) {
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
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + cond.hashCode();
			hashCode = 37 * hashCode + then.hashCode();
			hashCode = 37 * hashCode + elze.hashCode();
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
			final IfElseStmtImpl that = (IfElseStmtImpl) obj;
			return this.cond.equals(that.cond) && this.then.equals(that.then) && this.elze.equals(that.elze);
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
