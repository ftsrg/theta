package hu.bme.mit.inf.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Tuple3<T1, T2, T3> extends AbstractTuple implements Product3<T1, T2, T3> {

	Tuple3(final T1 e1, final T2 e2, final T3 e3) {
		super(e1, e2, e3);
		checkNotNull(e1);
		checkNotNull(e2);
		checkNotNull(e3);
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
