package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractTrueExpr extends AbstractBoolLitExpr implements TrueExpr {

	private static final int HASH_SEED = 242181;

	private static final String OPERATOR = "True";

	@Override
	public final boolean getValue() {
		return true;
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof TrueExpr);
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
