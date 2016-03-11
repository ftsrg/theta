package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractLeqExpr extends AbstractBinaryExpr<RatType, RatType, BoolType> implements LeqExpr {

	private static final String OPERATOR = "Leq";

	public AbstractLeqExpr(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 103;
	}

	@Override
	public final LeqExpr withOps(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final LeqExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final LeqExpr withRightOp(final Expr<? extends RatType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public final <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}