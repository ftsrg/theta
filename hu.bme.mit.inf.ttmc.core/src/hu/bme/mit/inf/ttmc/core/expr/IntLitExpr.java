package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.IntType;

public interface IntLitExpr extends LitExpr<IntType>, NullaryExpr<IntType>, Comparable<IntLitExpr> {
	public long getValue();
}
