package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.NullaryExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public final class NullExpr<PointedType extends Type> extends NullaryExpr<PointerType<PointedType>>
		implements LitExpr<PointerType<PointedType>> {

	private static final String EXPR_LABEL = "Null";
	private static final int HASH_SEED = 1632143;

	NullExpr() {
	}

	@Override
	public PointerType<PointedType> getType() {
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
