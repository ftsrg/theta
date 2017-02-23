package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class Prod3InitFunction<S1 extends State, S2 extends State, S3 extends State, P1 extends Prec, P2 extends Prec, P3 extends Prec>
		implements InitFunction<Prod3State<S1, S2, S3>, Prod3Prec<P1, P2, P3>> {

	private final InitFunction<S1, P1> initFunction1;
	private final InitFunction<S2, P2> initFunction2;
	private final InitFunction<S3, P3> initFunction3;

	private Prod3InitFunction(final InitFunction<S1, P1> initFunction1, final InitFunction<S2, P2> initFunction2,
			final InitFunction<S3, P3> initFunction3) {
		this.initFunction1 = checkNotNull(initFunction1);
		this.initFunction2 = checkNotNull(initFunction2);
		this.initFunction3 = checkNotNull(initFunction3);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3InitFunction<S1, S2, S3, P1, P2, P3> create(
			final InitFunction<S1, P1> initFunction1, final InitFunction<S2, P2> initFunction2,
			final InitFunction<S3, P3> initFunction3) {
		return new Prod3InitFunction<>(initFunction1, initFunction2, initFunction3);
	}

	@Override
	public Collection<? extends Prod3State<S1, S2, S3>> getInitStates(final Prod3Prec<P1, P2, P3> precision) {
		checkNotNull(precision);
		final Collection<? extends S1> initStates1 = initFunction1.getInitStates(precision._1());
		final Collection<? extends S2> initStates2 = initFunction2.getInitStates(precision._2());
		final Collection<? extends S3> initStates3 = initFunction3.getInitStates(precision._3());
		return ProdState.product(initStates1, initStates2, initStates3);
	}

}
