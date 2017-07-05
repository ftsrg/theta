package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.model.Substitution;

public final class FalseExpr extends BoolLitExpr {
	private static final FalseExpr INSTANCE = new FalseExpr();
	private static final int HASH_SEED = 712514;
	private static final String OPERATOR_LABEL = "False";

	private FalseExpr() {
	}

	static FalseExpr getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean getValue() {
		return false;
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(final Substitution assignment) {
		return this;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof FalseExpr);
	}

	@Override
	public String toString() {
		return OPERATOR_LABEL;
	}

}
