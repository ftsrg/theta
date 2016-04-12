package hu.bme.mit.inf.ttmc.core.expr.impl;

import hu.bme.mit.inf.ttmc.core.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public abstract class AbstractNullaryExpr<ExprType extends Type> extends AbstractExpr<ExprType>
		implements NullaryExpr<ExprType> {
}
