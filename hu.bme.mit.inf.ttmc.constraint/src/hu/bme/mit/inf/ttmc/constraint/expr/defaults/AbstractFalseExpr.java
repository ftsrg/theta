package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractFalseExpr extends AbstractBoolLitExpr implements FalseExpr {

	private static final int HASH_SEED = 712514;

	private static final String OPERATOR = "False";

	@Override
	public final boolean getValue() {
		return false;
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof FalseExpr);
	}

	@Override
	public final String toString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

}
