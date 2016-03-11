package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class IteExprImpl<ExprType extends Type> extends AbstractIteExpr<ExprType> {

	public IteExprImpl(Expr<? extends BoolType> cond, Expr<? extends ExprType> then, Expr<? extends ExprType> elze) {
		super(cond, then, elze);
	}

}
