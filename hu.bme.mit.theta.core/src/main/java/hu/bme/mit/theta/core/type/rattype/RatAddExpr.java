package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;

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
	public RatLitExpr eval(final Substitution assignment) {
		int sumNum = 0;
		int sumDenom = 1;
		for (final Expr<RatType> op : getOps()) {
			final RatLitExpr opLit = (RatLitExpr) op.eval(assignment);
			final int leftNum = sumNum;
			final int leftDenom = sumDenom;
			final int rightNum = opLit.getNum();
			final int rightDenom = opLit.getDenom();
			sumNum = leftNum * rightDenom + leftDenom * rightNum;
			sumDenom = leftDenom * rightDenom;
		}
		return Rat(sumNum, sumDenom);
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
