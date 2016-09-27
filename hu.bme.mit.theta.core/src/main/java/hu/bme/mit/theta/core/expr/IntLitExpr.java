package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;

public interface IntLitExpr extends LitExpr<IntType>, NullaryExpr<IntType>, Comparable<IntLitExpr> {
	public long getValue();

	public RatLitExpr toRatLit();
}
