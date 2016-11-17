package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkPositionIndex;

import java.util.Arrays;
import java.util.StringJoiner;

abstract class Tuple implements Product {

	private volatile int hashCode = 0;

	private final Object[] elems;

	Tuple(final Object... elems) {
		this.elems = elems;
	}

	////

	public static <T1, T2> Tuple1<T1> of(final T1 e1) {
		return new Tuple1<>(e1);
	}

	public static <T1, T2> Tuple2<T1, T2> of(final T1 e1, final T2 e2) {
		return new Tuple2<>(e1, e2);
	}

	public static <T1, T2, T3> Tuple3<T1, T2, T3> of(final T1 e1, final T2 e2, final T3 e3) {
		return new Tuple3<>(e1, e2, e3);
	}

	public static <T1, T2, T3, T4> Tuple4<T1, T2, T3, T4> of(final T1 e1, final T2 e2, final T3 e3, final T4 e4) {
		return new Tuple4<>(e1, e2, e3, e4);
	}

	public static <T1, T2, T3, T4, T5> Tuple5<T1, T2, T3, T4, T5> of(final T1 e1, final T2 e2, final T3 e3, final T4 e4,
			final T5 e5) {
		return new Tuple5<>(e1, e2, e3, e4, e5);
	}

	public static <T1, T2, T3, T4, T5, T6> Tuple6<T1, T2, T3, T4, T5, T6> of(final T1 e1, final T2 e2, final T3 e3,
			final T4 e4, final T5 e5, final T6 e6) {
		return new Tuple6<>(e1, e2, e3, e4, e5, e6);
	}

	public static <T1, T2, T3, T4, T5, T6, T7> Tuple7<T1, T2, T3, T4, T5, T6, T7> of(final T1 e1, final T2 e2,
			final T3 e3, final T4 e4, final T5 e5, final T6 e6, final T7 e7) {
		return new Tuple7<>(e1, e2, e3, e4, e5, e6, e7);
	}

	////

	@Override
	public final int arity() {
		return elems.length;
	}

	@Override
	public final Object elem(final int n) {
		checkPositionIndex(n, elems.length);
		return elems[n];
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = arity();
			result = 31 * hashCode + Arrays.hashCode(elems);
			hashCode = result;
		}
		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final Tuple that = (Tuple) obj;
			return Arrays.equals(this.elems, that.elems);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Tuple(", ")");
		for (final Object elem : elems) {
			sj.add(elem.toString());
		}
		return sj.toString();
	}

}
