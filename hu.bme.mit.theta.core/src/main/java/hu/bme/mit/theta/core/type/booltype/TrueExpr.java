package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.Types.Bool;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.ExprVisitor;

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
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
