package hu.bme.mit.theta.common;

import com.google.common.collect.ImmutableList;

public final class Tuple3<T1, T2, T3> extends Tuple implements Product3<T1, T2, T3> {

	Tuple3(final T1 e1, final T2 e2, final T3 e3) {
		super(ImmutableList.of(e1, e2, e3));
	}

	@Override
	public T1 _1() {
		@SuppressWarnings("unchecked")
		final T1 result = (T1) elem(0);
		return result;
	}

	@Override
	public T2 _2() {
		@SuppressWarnings("unchecked")
		final T2 result = (T2) elem(1);
		return result;
	}

	@Override
	public T3 _3() {
		@SuppressWarnings("unchecked")
		final T3 result = (T3) elem(2);
		return result;
	}

}
