package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public class RemExprImpl extends AbstractBinaryExpr<IntType, IntType, IntType> implements RemExpr {

	private static final String OPERATOR = "Rem";
		
	public RemExprImpl(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}
	
	@Override
	public RemExpr withOps(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RemExprImpl(leftOp, rightOp);
		}
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}
	
	@Override
	protected final int getHashSeed() {
		return 199;
	}

}