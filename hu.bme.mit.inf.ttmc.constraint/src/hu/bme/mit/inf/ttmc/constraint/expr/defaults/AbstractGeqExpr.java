package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractGeqExpr extends AbstractBinaryExpr<RatType, RatType, BoolType> implements GeqExpr {

	private static final String OPERATOR = "Geq";

	public AbstractGeqExpr(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public GeqExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public GeqExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public GeqExpr withRightOp(final Expr<? extends RatType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof GeqExpr) {
			final GeqExpr that = (GeqExpr) obj;
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
		return 59;
	}
}