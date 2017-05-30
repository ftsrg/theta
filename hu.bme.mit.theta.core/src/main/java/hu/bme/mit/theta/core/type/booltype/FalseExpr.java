package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

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
		return Types.Bool();
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
		return (obj instanceof FalseExpr);
	}

	@Override
	public String toString() {
		return OPERATOR_LABEL;
	}
}
