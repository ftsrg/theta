package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIteExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class IteExprImpl<ExprType extends Type> extends AbstractIteExpr<ExprType> {

	public IteExprImpl(final ConstraintManager manager, final Expr<? extends BoolType> cond,
			final Expr<? extends ExprType> then, final Expr<? extends ExprType> elze) {
		super(manager, cond, then, elze);
	}

}
