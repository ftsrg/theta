package hu.bme.mit.inf.ttmc.common.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.common.Tuple5;

public class Tuple5Impl<T1, T2, T3, T4, T5> extends AbstractTuple implements Tuple5<T1, T2, T3, T4, T5> {

	private final T1 e1;
	private final T2 e2;
	private final T3 e3;
	private final T4 e4;
	private final T5 e5;
	
	public Tuple5Impl(final T1 e1, final T2 e2, final T3 e3, final T4 e4, final T5 e5) {
		super(e1, e2, e3, e4, e5);
		this.e1 = checkNotNull(e1);
		this.e2 = checkNotNull(e2);
		this.e3 = checkNotNull(e3);
		this.e4 = checkNotNull(e4);
		this.e5 = checkNotNull(e5);
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
	public T5 _5() {
		return e5;
	}

	@Override
	public <T> Tuple5<T, T2, T3, T4, T5> with1(T e) {
		checkNotNull(e);
		return new Tuple5Impl<>(e, e2, e3, e4, e5);
	}

	@Override
	public <T> Tuple5<T1, T, T3, T4, T5> with2(T e) {
		checkNotNull(e);
		return new Tuple5Impl<>(e1, e, e3, e4, e5);
	}

	@Override
	public <T> Tuple5<T1, T2, T, T4, T5> with3(T e) {
		checkNotNull(e);
		return new Tuple5Impl<>(e1, e2, e, e4, e5);
	}

	@Override
	public <T> Tuple5<T1, T2, T3, T, T5> with4(T e) {
		checkNotNull(e);
		return new Tuple5Impl<>(e1, e2, e3, e, e5);
	}

	@Override
	public <T> Tuple5<T1, T2, T3, T4, T> with5(T e) {
		checkNotNull(e);
		return new Tuple5Impl<>(e1, e2, e3, e4, e);
	}

}
