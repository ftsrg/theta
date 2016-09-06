package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.IntType;

public interface IntLitExpr extends LitExpr<IntType>, NullaryExpr<IntType>, Comparable<IntLitExpr> {
	public long getValue();
}
