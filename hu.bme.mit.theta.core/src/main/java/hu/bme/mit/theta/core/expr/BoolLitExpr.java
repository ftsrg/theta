package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public abstract class BoolLitExpr extends NullaryExpr<BoolType> implements LitExpr<BoolType> {

	public abstract boolean getValue();

}
