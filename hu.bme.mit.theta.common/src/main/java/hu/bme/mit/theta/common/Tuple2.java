package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Tuple2<T1, T2> extends AbstractTuple implements Product2<T1, T2> {

	Tuple2(final T1 e1, final T2 e2) {
		super(e1, e2);
		checkNotNull(e1);
		checkNotNull(e2);
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

}
