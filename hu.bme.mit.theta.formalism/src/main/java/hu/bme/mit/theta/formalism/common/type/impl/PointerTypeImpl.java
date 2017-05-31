package hu.bme.mit.theta.formalism.common.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.common.expr.Exprs2.Null;

import java.util.Optional;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

final class PointerTypeImpl<PointedType extends Type> implements PointerType<PointedType> {

	private static final String TYPE_LABEL = "Pointer";

	private static final int HASH_SEED = 6619;
	private volatile int hashCode = 0;

	private final PointedType type;

	PointerTypeImpl(final PointedType type) {
		this.type = checkNotNull(type);
	}

	@Override
	public PointedType getPointedType() {
		return type;
	}

	@Override
	public LitExpr<? extends Type> getAny() {
		return Null();
	}

	@Override
	public boolean isLeq(final Type other) {
		if (other instanceof PointerType) {
			final PointerType<?> that = (PointerType<?>) other;
			return this.getPointedType().isLeq(that.getPointedType());
		} else {
			return false;
		}
	}

	@Override
	public Optional<? extends Type> meet(final Type type) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Optional<? extends Type> join(final Type type) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
		return ObjectUtils.toStringBuilder(TYPE_LABEL).add(type).toString();
	}

}
