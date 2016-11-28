package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface BoolLitExpr extends LitExpr<BoolType>, NullaryExpr<BoolType> {
	boolean getValue();

}
