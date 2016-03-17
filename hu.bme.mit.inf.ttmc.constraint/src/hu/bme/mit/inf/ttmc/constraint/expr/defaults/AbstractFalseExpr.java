package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractFalseExpr extends AbstractBoolLitExpr implements FalseExpr {

	private static final int HASH_SEED = 712514;

	private static final String OPERATOR_LABEL = "False";

	@SuppressWarnings("unused")
	private final ConstraintManager manager;

	public AbstractFalseExpr(final ConstraintManager manager) {
		this.manager = manager;
	}

	@Override
	public final boolean getValue() {
		return false;
	}

	@Override
	public final BoolType getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		return HASH_SEED;
	}

	@Override
	public final boolean equals(final Object obj) {
		return (obj instanceof FalseExpr);
	}

	@Override
	public final String toString() {
		return OPERATOR_LABEL;
	}

}
