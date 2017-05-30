package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.type.BoolType;

public abstract class BoolLitExpr extends NullaryExpr<BoolType> implements LitExpr<BoolType> {

	public abstract boolean getValue();

}
