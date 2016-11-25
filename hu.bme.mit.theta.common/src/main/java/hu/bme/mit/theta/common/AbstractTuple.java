package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkPositionIndex;

import java.util.Arrays;

abstract class AbstractTuple implements Product {

	private volatile int hashCode = 0;

	private final Object[] elems;

	protected AbstractTuple(final Object... elems) {
		this.elems = elems;
	}

	@Override
	public final int arity() {
		return elems.length;
	}

	@Override
	public final Object elem(final int n) {
		checkPositionIndex(n, elems.length);
		return elems[n];
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = arity();
			result = 31 * result + Arrays.hashCode(elems);
			hashCode = result;
		}
		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final AbstractTuple that = (AbstractTuple) obj;
			return Arrays.equals(this.elems, that.elems);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder("Tuple").addAll(elems).toString();
	}

}
