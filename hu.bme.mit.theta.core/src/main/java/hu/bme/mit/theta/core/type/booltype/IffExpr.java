package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.Types.Bool;

import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IffExpr extends EqExpr<BoolType> {

	private static final int HASH_SEED = 67;

	private static final String OPERATOR_LABEL = "Iff";

	IffExpr(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public IffExpr withOps(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new IffExpr(leftOp, rightOp);
		}
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
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IffExpr) {
			final IffExpr that = (IffExpr) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
