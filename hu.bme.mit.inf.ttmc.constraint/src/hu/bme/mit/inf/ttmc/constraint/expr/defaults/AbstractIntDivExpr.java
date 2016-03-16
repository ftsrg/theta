package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractIntDivExpr extends AbstractBinaryExpr<IntType, IntType, IntType> implements IntDivExpr {

	private static final String OPERATOR = "IDiv";

	public AbstractIntDivExpr(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public IntDivExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final IntDivExpr withLeftOp(final Expr<? extends IntType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final IntDivExpr withRightOp(final Expr<? extends IntType> rightOp) {
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
		} else if (obj instanceof IntDivExpr) {
			final IntDivExpr that = (IntDivExpr) obj;
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
	protected int getHashSeed() {
		return 79;
	}
}