package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public class RatDivExprImpl extends AbstractBinaryExpr<RatType, RatType, RatType> implements RatDivExpr {

	private static final String OPERATOR = "RDiv";
		
	public RatDivExprImpl(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public RatDivExpr withOps(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		return new RatDivExprImpl(leftOp, rightOp);
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 139;
	}
	
}