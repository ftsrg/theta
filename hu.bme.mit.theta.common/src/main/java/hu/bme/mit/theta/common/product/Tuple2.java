package hu.bme.mit.theta.common.product;

import com.google.common.collect.ImmutableList;

public final class Tuple2<T1, T2> extends Tuple implements Product2<T1, T2> {

	Tuple2(final T1 e1, final T2 e2) {
		super(ImmutableList.of(e1, e2));
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
