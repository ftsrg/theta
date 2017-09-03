package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class Prod3InitFunc<S1 extends State, S2 extends State, S3 extends State, P1 extends Prec, P2 extends Prec, P3 extends Prec>
		implements InitFunc<Prod3State<S1, S2, S3>, Prod3Prec<P1, P2, P3>> {

	private final InitFunc<S1, P1> initFunc1;
	private final InitFunc<S2, P2> initFunc2;
	private final InitFunc<S3, P3> initFunc3;

	private Prod3InitFunc(final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2,
			final InitFunc<S3, P3> initFunc3) {
		this.initFunc1 = checkNotNull(initFunc1);
		this.initFunc2 = checkNotNull(initFunc2);
		this.initFunc3 = checkNotNull(initFunc3);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3InitFunc<S1, S2, S3, P1, P2, P3> create(
			final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2, final InitFunc<S3, P3> initFunc3) {
		return new Prod3InitFunc<>(initFunc1, initFunc2, initFunc3);
	}

	@Override
	public Collection<? extends Prod3State<S1, S2, S3>> getInitStates(final Prod3Prec<P1, P2, P3> prec) {
		checkNotNull(prec);
		final Collection<? extends S1> initStates1 = initFunc1.getInitStates(prec._1());
		final Collection<? extends S2> initStates2 = initFunc2.getInitStates(prec._2());
		final Collection<? extends S3> initStates3 = initFunc3.getInitStates(prec._3());
		return ProdState.product(initStates1, initStates2, initStates3);
	}

}
