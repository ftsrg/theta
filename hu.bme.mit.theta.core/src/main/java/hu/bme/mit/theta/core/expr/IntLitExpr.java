package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;

public interface IntLitExpr extends LitExpr<IntType>, NullaryExpr<IntType>, Comparable<IntLitExpr> {
	long getValue();

	RatLitExpr toRatLit();
}
