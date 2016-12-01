package hu.bme.mit.theta.core.expr.impl;

import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public abstract class AbstractNullaryExpr<ExprType extends Type> extends AbstractExpr<ExprType>
		implements NullaryExpr<ExprType> {
}
