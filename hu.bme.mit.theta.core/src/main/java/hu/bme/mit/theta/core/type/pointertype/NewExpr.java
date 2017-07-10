package hu.bme.mit.theta.core.type.pointertype;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.pointertype.PointerExprs.Pointer;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.NullaryExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.model.Valuation;

public final class NewExpr<PointedType extends Type> extends NullaryExpr<PointerType<PointedType>> {

	private static final int HASH_SEED = 8699;
	private volatile int hashCode = 0;

	private static final String EXPR_LABEL = "New";

	private final PointedType pointedType;

	NewExpr(final PointedType pointedType) {
		this.pointedType = checkNotNull(pointedType);
	}

	public PointedType getPointedType() {
		return pointedType;
	}

	@Override
	public PointerType<PointedType> getType() {
		return Pointer(pointedType);
	}

	@Override
	public LitExpr<PointerType<PointedType>> eval(final Valuation val) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + pointedType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof NewExpr) {
			final NewExpr<?> that = (NewExpr<?>) obj;
			return this.getPointedType().equals(that.getPointedType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(EXPR_LABEL).add(pointedType).toString();
	}

}
