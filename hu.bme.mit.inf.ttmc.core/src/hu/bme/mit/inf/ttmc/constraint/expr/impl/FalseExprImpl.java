package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.impl.Types;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

final class FalseExprImpl extends AbstractBoolLitExpr implements FalseExpr {

	private static final int HASH_SEED = 712514;

	private static final String OPERATOR_LABEL = "False";

	FalseExprImpl() {
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
