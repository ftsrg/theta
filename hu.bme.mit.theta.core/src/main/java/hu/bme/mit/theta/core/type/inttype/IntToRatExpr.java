package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.abstracttype.CastExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class IntToRatExpr extends CastExpr<IntType, RatType> {

	private static final int HASH_SEED = 1627;
	private static final String OPERATOR_LABEL = "ToRat";

	IntToRatExpr(final Expr<IntType> op) {
		super(op);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatLitExpr eval(final Substitution assignment) {
		final IntLitExpr opVal = (IntLitExpr) getOp().eval(assignment);
		return opVal.toRat();
	}

	@Override
	public IntToRatExpr with(final Expr<IntType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new IntToRatExpr(op);
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
