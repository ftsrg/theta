package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.model.Valuation;

public final class TrueExpr extends BoolLitExpr {
	private static final TrueExpr INSTANCE = new TrueExpr();
	private static final int HASH_SEED = 242181;
	private static final String OPERATOR = "True";

	private TrueExpr() {
	}

	static TrueExpr getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean getValue() {
		return true;
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		return this;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof TrueExpr);
	}

	@Override
	public String toString() {
		return OPERATOR;
	}

}
