package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractImplyExpr extends AbstractBinaryExpr<BoolType, BoolType, BoolType> implements ImplyExpr {

	private static final String OPERATOR = "Imply";

	public AbstractImplyExpr(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public final ImplyExpr withOps(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final ImplyExpr withLeftOp(final Expr<? extends BoolType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final ImplyExpr withRightOp(final Expr<? extends BoolType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ImplyExpr) {
			final ImplyExpr that = (ImplyExpr) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
		} else {
			return false;
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
