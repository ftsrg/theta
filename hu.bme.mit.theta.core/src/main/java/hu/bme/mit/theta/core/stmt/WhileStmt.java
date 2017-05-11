package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class WhileStmt implements Stmt {

	private final static int HASH_SEED = 631;
	private volatile int hashCode = 0;

	private final Expr<? extends BoolType> cond;
	private final Stmt doStmt;

	WhileStmt(final Expr<? extends BoolType> cond, final Stmt doStmt) {
		this.cond = checkNotNull(cond);
		this.doStmt = checkNotNull(doStmt);
	}

	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	public Stmt getDo() {
		return doStmt;
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
		return ObjectUtils.toStringBuilder("While").add(cond).add(doStmt).toString();
	}
}
