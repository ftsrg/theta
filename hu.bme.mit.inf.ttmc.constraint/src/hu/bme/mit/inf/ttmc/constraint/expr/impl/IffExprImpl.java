package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IffExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class IffExprImpl extends AbstractBinaryExpr<BoolType, BoolType, BoolType>
		implements IffExpr {

	private static final String OPERATOR = "Iff";

	public IffExprImpl(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
	}
	
	@Override
	public IffExpr withOps(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new IffExprImpl(leftOp, rightOp);
		}
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 67;
	}

	@Override
	public IffExpr withLeftOp(final Expr<? extends BoolType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public IffExpr withRightOp(final Expr<? extends BoolType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
