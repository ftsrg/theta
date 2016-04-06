package hu.bme.mit.inf.ttmc.common.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.common.Tuple3;

public class Tuple3Impl<T1, T2, T3> extends AbstractTuple implements Tuple3<T1, T2, T3> {

	private final T1 e1;
	private final T2 e2;
	private final T3 e3;
	
	public Tuple3Impl(final T1 e1, final T2 e2, final T3 e3) {
		super(e1, e2, e3);
		this.e1 = checkNotNull(e1);
		this.e2 = checkNotNull(e2);
		this.e3 = checkNotNull(e3);
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
	public <T> Tuple3<T, T2, T3> with1(T e) {
		checkNotNull(e);
		return new Tuple3Impl<>(e, e2, e3);
	}

	@Override
	public <T> Tuple3<T1, T, T3> with2(T e) {
		checkNotNull(e);
		return new Tuple3Impl<>(e1, e, e3);
	}

	@Override
	public <T> Tuple3<T1, T2, T> with3(T e) {
		checkNotNull(e);
		return new Tuple3Impl<>(e1, e2, e);
	}

}
