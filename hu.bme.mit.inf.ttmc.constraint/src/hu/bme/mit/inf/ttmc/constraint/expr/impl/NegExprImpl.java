package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public final class NegExprImpl<ExprType extends ClosedUnderNeg> extends AbstractUnaryExpr<ExprType, ExprType>
		implements NegExpr<ExprType> {

	private static final int HASH_SEED = 97;

	private static final String OPERATOR_LABEL = "Neg";

	private final ConstraintManager manager;

	public NegExprImpl(final ConstraintManager manager, final Expr<? extends ExprType> op) {
		super(op);
		this.manager = manager;
	}

	@Override
	public ExprType getType() {
		return getOp().getType();
	}

	@Override
	public NegExpr<ExprType> withOp(final Expr<? extends ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return manager.getExprFactory().Neg(op);
		}
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof NegExpr<?>) {
			final NegExpr<?> that = (NegExpr<?>) obj;
			return this.getOp().equals(that.getOp());
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
