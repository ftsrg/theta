package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

final class Prod2TransferFunction<S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision>
		implements TransferFunction<Prod2State<S1, S2>, A, Prod2Precision<P1, P2>> {

	private final TransferFunction<S1, ? super A, P1> transferFunction1;
	private final TransferFunction<S2, ? super A, P2> transferFunction2;
	private final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator;

	private Prod2TransferFunction(final TransferFunction<S1, ? super A, P1> transferFunction1,
			final TransferFunction<S2, ? super A, P2> transferFunction2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		this.transferFunction1 = checkNotNull(transferFunction1);
		this.transferFunction2 = checkNotNull(transferFunction2);
		this.strenghteningOperator = checkNotNull(strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision> Prod2TransferFunction<S1, S2, A, P1, P2> create(
			final TransferFunction<S1, A, P1> transferFunction1, final TransferFunction<S2, A, P2> transferFunction2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		return new Prod2TransferFunction<>(transferFunction1, transferFunction2, strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision> Prod2TransferFunction<S1, S2, A, P1, P2> create(
			final TransferFunction<S1, ? super A, P1> transferFunction1,
			final TransferFunction<S2, ? super A, P2> transferFunction2) {
		return new Prod2TransferFunction<>(transferFunction1, transferFunction2, (states, precision) -> states);
	}

	@Override
	public Collection<? extends Prod2State<S1, S2>> getSuccStates(final Prod2State<S1, S2> state,
			final A action, final Prod2Precision<P1, P2> precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);

		final Collection<? extends S1> succStates1 = transferFunction1.getSuccStates(state._1(), action,
				precision._1());
		final Collection<? extends S2> succStates2 = transferFunction2.getSuccStates(state._2(), action,
				precision._2());
		final Collection<Prod2State<S1, S2>> compositeIniStates = Prod2State.product(succStates1, succStates2);
		return strenghteningOperator.strengthen(compositeIniStates, precision);
	}

}
