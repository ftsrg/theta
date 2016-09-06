package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.BoolType;

public interface BoolLitExpr extends LitExpr<BoolType>, NullaryExpr<BoolType> {
	public boolean getValue();

}
