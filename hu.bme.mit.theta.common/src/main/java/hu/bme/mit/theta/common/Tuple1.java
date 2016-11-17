package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Tuple1<T1> extends Tuple implements Product1<T1> {

	Tuple1(final T1 e1) {
		super(e1);
		checkNotNull(e1);
	}

	@Override
	public T1 _1() {
		@SuppressWarnings("unchecked")
		final T1 result = (T1) elem(0);
		return result;
	}

}
