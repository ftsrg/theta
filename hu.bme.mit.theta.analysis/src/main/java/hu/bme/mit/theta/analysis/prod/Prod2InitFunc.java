package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class Prod2InitFunc<S1 extends State, S2 extends State, P1 extends Prec, P2 extends Prec>
		implements InitFunc<Prod2State<S1, S2>, Prod2Prec<P1, P2>> {

	private final InitFunc<S1, P1> initFunc1;
	private final InitFunc<S2, P2> initFunc2;
	private final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator;

	private Prod2InitFunc(final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		this.initFunc1 = checkNotNull(initFunc1);
		this.initFunc2 = checkNotNull(initFunc2);
		this.strenghteningOperator = checkNotNull(strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, P1 extends Prec, P2 extends Prec> Prod2InitFunc<S1, S2, P1, P2> create(
			final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		return new Prod2InitFunc<>(initFunc1, initFunc2, strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, P1 extends Prec, P2 extends Prec> Prod2InitFunc<S1, S2, P1, P2> create(
			final InitFunc<S1, P1> initFunc1, final InitFunc<S2, P2> initFunc2) {
		return new Prod2InitFunc<>(initFunc1, initFunc2, (states, prec) -> states);
	}

	@Override
	public Collection<? extends Prod2State<S1, S2>> getInitStates(final Prod2Prec<P1, P2> prec) {
		checkNotNull(prec);

		final Collection<? extends S1> initStates1 = initFunc1.getInitStates(prec._1());
		final Collection<? extends S2> initStates2 = initFunc2.getInitStates(prec._2());
		final Collection<Prod2State<S1, S2>> compositeIniStates = ProdState.product(initStates1, initStates2);
		return strenghteningOperator.strengthen(compositeIniStates, prec);
	}

}
