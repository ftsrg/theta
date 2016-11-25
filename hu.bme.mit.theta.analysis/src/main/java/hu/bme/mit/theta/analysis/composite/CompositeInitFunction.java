package hu.bme.mit.theta.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

final class CompositeInitFunction<S1 extends State, S2 extends State, P1 extends Precision, P2 extends Precision>
		implements InitFunction<CompositeState<S1, S2>, CompositePrecision<P1, P2>> {

	private final InitFunction<S1, P1> initFunction1;
	private final InitFunction<S2, P2> initFunction2;
	private final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator;

	private CompositeInitFunction(final InitFunction<S1, P1> initFunction1, final InitFunction<S2, P2> initFunction2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		this.initFunction1 = checkNotNull(initFunction1);
		this.initFunction2 = checkNotNull(initFunction2);
		this.strenghteningOperator = checkNotNull(strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, P1 extends Precision, P2 extends Precision> CompositeInitFunction<S1, S2, P1, P2> create(
			final InitFunction<S1, P1> initFunction1, final InitFunction<S2, P2> initFunction2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		return new CompositeInitFunction<>(initFunction1, initFunction2, strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, P1 extends Precision, P2 extends Precision> CompositeInitFunction<S1, S2, P1, P2> create(
			final InitFunction<S1, P1> initFunction1, final InitFunction<S2, P2> initFunction2) {
		return new CompositeInitFunction<>(initFunction1, initFunction2, (states, precision) -> states);
	}

	@Override
	public Collection<? extends CompositeState<S1, S2>> getInitStates(final CompositePrecision<P1, P2> precision) {
		checkNotNull(precision);

		final Collection<? extends S1> initStates1 = initFunction1.getInitStates(precision._1());
		final Collection<? extends S2> initStates2 = initFunction2.getInitStates(precision._2());
		final Collection<CompositeState<S1, S2>> compositeIniStates = CompositeState.product(initStates1, initStates2);
		return strenghteningOperator.strengthen(compositeIniStates, precision);
	}

}
