package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.MultiaryExpr;

public abstract class MulExpr<ExprType extends Multiplicative<ExprType>> extends MultiaryExpr<ExprType, ExprType> {

	protected MulExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
