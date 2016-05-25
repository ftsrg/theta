package hu.bme.mit.inf.ttmc.common;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Tuple4<T1, T2, T3, T4> extends AbstractTuple implements Product4<T1, T2, T3, T4> {

	Tuple4(final T1 e1, final T2 e2, final T3 e3, final T4 e4) {
		super(e1, e2, e3, e4);
		checkNotNull(e1);
		checkNotNull(e2);
		checkNotNull(e3);
		checkNotNull(e4);
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

	@Override
	public T4 _4() {
		@SuppressWarnings("unchecked")
		final T4 result = (T4) elem(3);
		return result;
	}

}
