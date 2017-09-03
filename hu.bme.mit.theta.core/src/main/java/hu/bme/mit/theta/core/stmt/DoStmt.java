package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class DoStmt implements Stmt {

	private static final int HASH_SEED = 599;
	private volatile int hashCode = 0;

	private final Stmt doStmt;
	private final Expr<BoolType> cond;

	DoStmt(final Stmt doStmt, final Expr<BoolType> cond) {
		this.doStmt = checkNotNull(doStmt);
		this.cond = checkNotNull(cond);
	}

	public Stmt getDo() {
		return doStmt;
	}

	public Expr<BoolType> getCond() {
		return cond;
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
		return Utils.toStringBuilder("Do").add(doStmt).add(cond).toString();
	}
}
