package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class ImplyExprImpl extends AbstractBinaryExpr<BoolType, BoolType, BoolType> implements ImplyExpr {

	private static final String OPERATOR = "Imply";

	public ImplyExprImpl(final Expr<? extends BoolType> leftOp,
			final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public ImplyExpr withOps(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new ImplyExprImpl(leftOp, rightOp);
		}
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 71;
	}
}
