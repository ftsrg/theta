package hu.bme.mit.theta.core.type.pointertype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Type;

public final class PointerType<PointedType extends Type> implements Type {

	private static final String TYPE_LABEL = "Pointer";

	private static final int HASH_SEED = 6619;
	private volatile int hashCode = 0;

	private final PointedType type;

	PointerType(final PointedType type) {
		this.type = checkNotNull(type);
	}

	public PointedType getPointedType() {
		return type;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + type.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof PointerType) {
			final PointerType<?> that = (PointerType<?>) obj;
			return this.getPointedType().equals(that.getPointedType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(TYPE_LABEL).add(type).toString();
	}

}
