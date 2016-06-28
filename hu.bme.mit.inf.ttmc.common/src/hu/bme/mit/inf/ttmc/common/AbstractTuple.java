package hu.bme.mit.inf.ttmc.common;

import static com.google.common.base.Preconditions.checkPositionIndex;

import java.util.StringJoiner;

abstract class AbstractTuple implements Product {

	private volatile int hashCode = 0;

	private final Object[] elems;

	protected AbstractTuple(final Object... elems) {
		this.elems = elems;
	}

	@Override
	public int arity() {
		return elems.length;
	}

	@Override
	public Object elem(final int n) {
		checkPositionIndex(n, elems.length);
		return elems[n];
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = arity();
			result = 31 * hashCode + elems.hashCode();
			hashCode = result;
		}
		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final AbstractTuple that = (AbstractTuple) obj;
			return this.elems.equals(that.elems);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Tuple(", ")");
		for (final Object elem : elems) {
			sj.add(elem.toString());
		}
		return sj.toString();
	}

}
