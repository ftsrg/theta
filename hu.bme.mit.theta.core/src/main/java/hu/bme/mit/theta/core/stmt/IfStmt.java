package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class IfStmt implements Stmt {

	private static final int HASH_SEED = 829;
	private volatile int hashCode = 0;

	private final Expr<BoolType> cond;
	private final Stmt then;

	IfStmt(final Expr<BoolType> cond, final Stmt then) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
	}

	public Expr<BoolType> getCond() {
		return cond;
	}

	public Stmt getThen() {
		return then;
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
			result = 31 * result + then.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IfStmt) {
			final IfStmt that = (IfStmt) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder("If").add(cond).add(then).toString();
	}

}
