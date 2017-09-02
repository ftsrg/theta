package hu.bme.mit.theta.core.type.pointertype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public final class NullExpr<PointedType extends Type> extends NullaryExpr<PointerType<PointedType>>
		implements LitExpr<PointerType<PointedType>> {

	private static final NullExpr<?> INSTANCE = new NullExpr<>();
	private static final String EXPR_LABEL = "Null";
	private static final int HASH_SEED = 1632143;

	private NullExpr() {
	}

	@SuppressWarnings("unchecked")
	static <PointedType extends Type> NullExpr<PointedType> getInstance() {
		return (NullExpr<PointedType>) INSTANCE;
	}

	@Override
	public PointerType<PointedType> getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public LitExpr<PointerType<PointedType>> eval(final Valuation val) {
		return this;
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
