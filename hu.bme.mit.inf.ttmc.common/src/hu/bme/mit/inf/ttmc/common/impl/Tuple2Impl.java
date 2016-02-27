package hu.bme.mit.inf.ttmc.common.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.common.Tuple2;

public class Tuple2Impl<T1, T2> extends AbstractTuple implements Tuple2<T1, T2> {

	private final T1 e1;
	private final T2 e2;
	
	public Tuple2Impl(final T1 e1, final T2 e2) {
		super(e1, e2);
		this.e1 = checkNotNull(e1);
		this.e2 = checkNotNull(e2);
	}

	@Override
	public T1 _1() {
		return e1;
	}

	@Override
	public T2 _2() {
		return e2;
	}

	@Override
	public <T> Tuple2<T, T2> with1(T e) {
		checkNotNull(e);
		return new Tuple2Impl<>(e, e2);
	}

	@Override
	public <T> Tuple2<T1, T> with2(T e) {
		checkNotNull(e);
		return new Tuple2Impl<>(e1, e);
	}

}
