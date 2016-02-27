package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractNullaryExpr<ExprType extends Type> extends AbstractExpr<ExprType> implements NullaryExpr<ExprType> {
	
	@Override
	public int hashCode() {
		return getHashSeed();
	}
}
