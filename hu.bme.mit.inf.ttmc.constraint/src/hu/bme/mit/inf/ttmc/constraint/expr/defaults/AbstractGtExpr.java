package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.GtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractBinaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractGtExpr extends AbstractBinaryExpr<RatType, RatType, BoolType>
		implements GtExpr {

	private static final String OPERATOR = "Gt";

	public AbstractGtExpr(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 61;
	}
	
	@Override
	public GtExpr withOps(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	@Override
	public GtExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public GtExpr withRightOp(final Expr<? extends RatType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}
	
	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
