package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractNegExpr<ExprType extends ClosedUnderNeg> extends AbstractUnaryExpr<ExprType, ExprType>
		implements NegExpr<ExprType> {

	private static final int HASH_SEED = 97;

	private static final String OPERATOR_LABEL = "Neg";

	public AbstractNegExpr(final Expr<? extends ExprType> op) {
		super(op);
	}

	@Override
	public final NegExpr<ExprType> withOp(final Expr<? extends ExprType> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
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
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
