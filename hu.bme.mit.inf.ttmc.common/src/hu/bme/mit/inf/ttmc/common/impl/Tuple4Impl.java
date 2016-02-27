package hu.bme.mit.inf.ttmc.common.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.common.Tuple4;

public class Tuple4Impl<T1, T2, T3, T4> extends AbstractTuple implements Tuple4<T1, T2, T3, T4> {

	private final T1 e1;
	private final T2 e2;
	private final T3 e3;
	private final T4 e4;
	
	public Tuple4Impl(final T1 e1, final T2 e2, final T3 e3, final T4 e4) {
		super(e1, e2, e3, e4);
		this.e1 = checkNotNull(e1);
		this.e2 = checkNotNull(e2);
		this.e3 = checkNotNull(e3);
		this.e4 = checkNotNull(e4);
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
	public T3 _3() {
		return e3;
	}
	
	@Override
	public T4 _4() {
		return e4;
	}

	@Override
	public <T> Tuple4<T, T2, T3, T4> with1(T e) {
		checkNotNull(e);
		return new Tuple4Impl<>(e, e2, e3, e4);
	}

	@Override
	public <T> Tuple4<T1, T, T3, T4> with2(T e) {
		checkNotNull(e);
		return new Tuple4Impl<>(e1, e, e3, e4);
	}

	@Override
	public <T> Tuple4<T1, T2, T, T4> with3(T e) {
		checkNotNull(e);
		return new Tuple4Impl<>(e1, e2, e, e4);
	}

	@Override
	public <T> Tuple4<T1, T2, T3, T> with4(T e) {
		checkNotNull(e);
		return new Tuple4Impl<>(e1, e2, e3, e);
	}

}
