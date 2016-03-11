package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractGeqExpr extends AbstractBinaryExpr<RatType, RatType, BoolType>
		implements GeqExpr {

	private static final String OPERATOR = "Geq";

	public AbstractGeqExpr(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 59;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
	@Override
	public GeqExpr withOps(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
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
}