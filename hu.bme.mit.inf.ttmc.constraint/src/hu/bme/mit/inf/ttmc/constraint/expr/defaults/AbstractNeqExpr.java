package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractNeqExpr extends AbstractBinaryExpr<Type, Type, BoolType> implements NeqExpr {

	private static final String OPERATOR = "Neq";

	public AbstractNeqExpr(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 113;
	}

	@Override
	public NeqExpr withOps(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public NeqExpr withLeftOp(final Expr<? extends Type> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public NeqExpr withRightOp(final Expr<? extends Type> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
