package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class ReturnStmt<ReturnType extends Type> implements Stmt {

	private static final int HASH_SEED = 1009;
	private volatile int hashCode = 0;

	private final Expr<ReturnType> expr;

	ReturnStmt(final Expr<ReturnType> expr) {
		this.expr = checkNotNull(expr);
	}

	public Expr<ReturnType> getExpr() {
		return expr;
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
			result = 31 * result + expr.hashCode();
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
		return ObjectUtils.toStringBuilder("Return").add(expr).toString();
	}

}
