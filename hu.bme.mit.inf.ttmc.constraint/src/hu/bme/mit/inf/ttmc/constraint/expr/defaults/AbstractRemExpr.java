package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractRemExpr extends AbstractBinaryExpr<IntType, IntType, IntType> implements RemExpr {

	private static final String OPERATOR = "Rem";

	public AbstractRemExpr(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 199;
	}

	@Override
	public RemExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public RemExpr withLeftOp(final Expr<? extends IntType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public RemExpr withRightOp(final Expr<? extends IntType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}
}