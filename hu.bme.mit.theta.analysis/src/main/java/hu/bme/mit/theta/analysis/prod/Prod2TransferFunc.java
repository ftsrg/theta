package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;

final class Prod2TransferFunc<S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec>
		implements TransferFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> {

	private final TransferFunc<S1, ? super A, P1> transferFunc1;
	private final TransferFunc<S2, ? super A, P2> transferFunc2;
	private final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator;

	private Prod2TransferFunc(final TransferFunc<S1, ? super A, P1> transferFunc1,
			final TransferFunc<S2, ? super A, P2> transferFunc2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		this.transferFunc1 = checkNotNull(transferFunc1);
		this.transferFunc2 = checkNotNull(transferFunc2);
		this.strenghteningOperator = checkNotNull(strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2TransferFunc<S1, S2, A, P1, P2> create(
			final TransferFunc<S1, A, P1> transferFunc1, final TransferFunc<S2, A, P2> transferFunc2,
			final StrengtheningOperator<S1, S2, P1, P2> strenghteningOperator) {
		return new Prod2TransferFunc<>(transferFunc1, transferFunc2, strenghteningOperator);
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2TransferFunc<S1, S2, A, P1, P2> create(
			final TransferFunc<S1, ? super A, P1> transferFunc1, final TransferFunc<S2, ? super A, P2> transferFunc2) {
		return new Prod2TransferFunc<>(transferFunc1, transferFunc2, (states, prec) -> states);
	}

	@Override
	public Collection<? extends Prod2State<S1, S2>> getSuccStates(final Prod2State<S1, S2> state, final A action,
			final Prod2Prec<P1, P2> prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final Collection<? extends S1> succStates1 = transferFunc1.getSuccStates(state._1(), action, prec._1());
		final Collection<? extends S2> succStates2 = transferFunc2.getSuccStates(state._2(), action, prec._2());
		final Collection<Prod2State<S1, S2>> compositeIniStates = ProdState.product(succStates1, succStates2);
		return strenghteningOperator.strengthen(compositeIniStates, prec);
	}

}
