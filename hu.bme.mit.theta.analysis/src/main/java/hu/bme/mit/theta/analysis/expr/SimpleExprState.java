package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

final class SimpleExprState implements ExprState {

	private final Expr<BoolType> expr;

	private SimpleExprState(final Expr<BoolType> expr) {
		this.expr = checkNotNull(expr);
	}

	public static SimpleExprState of(final Expr<BoolType> expr) {
		return new SimpleExprState(expr);
	}

	@Override
	public Expr<BoolType> toExpr() {
		return expr;
	}

}
