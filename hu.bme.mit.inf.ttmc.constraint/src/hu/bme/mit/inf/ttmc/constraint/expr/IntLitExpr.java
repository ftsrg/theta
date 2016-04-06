package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public interface IntLitExpr extends NullaryExpr<IntType>, Comparable<IntLitExpr> {
	public long getValue();
}
