package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class IfElseStmt implements Stmt {

	private static final int HASH_SEED = 661;
	private volatile int hashCode = 0;

	private final Expr<BoolType> cond;
	private final Stmt then;
	private final Stmt elze;

	IfElseStmt(final Expr<BoolType> cond, final Stmt then, final Stmt elze) {
		this.cond = checkNotNull(cond);
		this.then = checkNotNull(then);
		this.elze = checkNotNull(elze);
	}

	public Expr<BoolType> getCond() {
		return cond;
	}

	public Stmt getThen() {
		return then;
	}

	public Stmt getElse() {
		return elze;
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
			result = 31 * result + elze.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IfElseStmt) {
			final IfElseStmt that = (IfElseStmt) obj;
			return this.getCond().equals(that.getCond()) && this.getThen().equals(that.getThen())
					&& this.getElse().equals(that.getElse());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("If").add(cond).add(then).add(elze).toString();
	}
}
