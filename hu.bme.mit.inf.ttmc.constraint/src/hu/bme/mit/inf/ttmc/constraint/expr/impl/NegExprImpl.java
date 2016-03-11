package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNegExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;

public final class NegExprImpl<ExprType extends ClosedUnderNeg> extends AbstractNegExpr<ExprType> {

	public NegExprImpl(Expr<? extends ExprType> op) {
		super(op);
	}

}
