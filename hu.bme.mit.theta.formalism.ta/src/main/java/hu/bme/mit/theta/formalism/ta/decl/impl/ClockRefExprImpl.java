package hu.bme.mit.theta.formalism.ta.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.expr.ClockRefExpr;

final class ClockRefExprImpl extends ClockRefExpr {

	private static final int HASH_SEED = 1951;

	private final ClockDecl decl;

	private volatile int hashCode = 0;

	ClockRefExprImpl(final ClockDecl clockDecl) {
		this.decl = checkNotNull(clockDecl);
	}

	@Override
	public ClockDecl getDecl() {
		return decl;
	}

	@Override
	public RatType getType() {
		return decl.getType();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit((VarRefExpr<RatType>) this, param);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + decl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ClockRefExpr) {
			final ClockRefExpr that = (ClockRefExpr) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return getDecl().getName();
	}

}
