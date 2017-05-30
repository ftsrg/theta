package hu.bme.mit.theta.core.type.rattype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.RatType;

public final class RatExprs {

	private RatExprs() {
	}

	public static RatLitExpr Rat(final int num, final int denom) {
		return new RatLitExpr(num, denom);
	}

	public static RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new RatDivExpr(leftOp, rightOp);
	}

}
