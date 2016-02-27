package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public class IntDivExprImpl extends AbstractBinaryExpr<IntType, IntType, IntType>
		implements IntDivExpr {

	private static final String OPERATOR = "IDiv";

	public IntDivExprImpl(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}
	
	@Override
	public IntDivExpr withOps(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new IntDivExprImpl(leftOp, rightOp);
		}
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return 79;
	}

}