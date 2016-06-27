package hu.bme.mit.inf.ttmc.formalism.common.expr.impl;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.NullExpr;
import hu.bme.mit.inf.ttmc.formalism.common.type.PointerType;

final class NullExprImpl<PointedType extends Type> implements NullExpr<PointedType> {

	private static final String EXPR_LABEL = "Null";
	private static final int HASH_SEED = 1632143;

	NullExprImpl() {
	}

	@Override
	public PointerType<PointedType> getType() {
		throw new UnsupportedOperationException();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof NullExpr);
	}

	@Override
	public String toString() {
		return EXPR_LABEL;
	}

}
