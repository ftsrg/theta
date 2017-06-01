package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class RatAddExpr extends AddExpr<RatType> {

	private static final int HASH_SEED = 4909;
	private static final String OPERATOR_LABEL = "Add";

	RatAddExpr(final Iterable<? extends Expr<RatType>> ops) {
		super(ops);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatAddExpr with(final Iterable<? extends Expr<RatType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new RatAddExpr(ops);
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
		} else if (obj instanceof RatAddExpr) {
			final RatAddExpr that = (RatAddExpr) obj;
			return this.getOps().equals(that.getOps());
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
