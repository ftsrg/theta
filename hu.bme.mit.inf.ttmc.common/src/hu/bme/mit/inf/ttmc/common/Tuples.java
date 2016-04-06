package hu.bme.mit.inf.ttmc.common;

import hu.bme.mit.inf.ttmc.common.impl.Tuple2Impl;
import hu.bme.mit.inf.ttmc.common.impl.Tuple3Impl;
import hu.bme.mit.inf.ttmc.common.impl.Tuple4Impl;
import hu.bme.mit.inf.ttmc.common.impl.Tuple5Impl;
import hu.bme.mit.inf.ttmc.common.impl.Tuple6Impl;
import hu.bme.mit.inf.ttmc.common.impl.Tuple7Impl;

public class Tuples {
	
	private Tuples() {
	}

	public static <T1, T2> Tuple2<T1, T2> of(final T1 e1, final T2 e2) {
		return new Tuple2Impl<>(e1, e2);
	}

	public static <T1, T2, T3> Tuple3<T1, T2, T3> of(final T1 e1, final T2 e2, final T3 e3) {
		return new Tuple3Impl<>(e1, e2, e3);
	}

	public static <T1, T2, T3, T4> Tuple4<T1, T2, T3, T4> of(final T1 e1, final T2 e2, final T3 e3, final T4 e4) {
		return new Tuple4Impl<>(e1, e2, e3, e4);
	}

	public static <T1, T2, T3, T4, T5> Tuple5<T1, T2, T3, T4, T5> of(final T1 e1, final T2 e2, final T3 e3, final T4 e4,
			final T5 e5) {
		return new Tuple5Impl<>(e1, e2, e3, e4, e5);
	}

	public static <T1, T2, T3, T4, T5, T6> Tuple6<T1, T2, T3, T4, T5, T6> of(final T1 e1, final T2 e2, final T3 e3,
			final T4 e4, final T5 e5, final T6 e6) {
		return new Tuple6Impl<>(e1, e2, e3, e4, e5, e6);
	}

	public static <T1, T2, T3, T4, T5, T6, T7> Tuple7<T1, T2, T3, T4, T5, T6, T7> of(final T1 e1, final T2 e2,
			final T3 e3, final T4 e4, final T5 e5, final T6 e6, final T7 e7) {
		return new Tuple7Impl<>(e1, e2, e3, e4, e5, e6, e7);
	}

}
