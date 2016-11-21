package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

final class Prod3TransferFunction<S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Precision, P2 extends Precision, P3 extends Precision>
		implements TransferFunction<Prod3State<S1, S2, S3>, A, Prod3Precision<P1, P2, P3>> {

	private final TransferFunction<S1, ? super A, P1> transferFunction1;
	private final TransferFunction<S2, ? super A, P2> transferFunction2;
	private final TransferFunction<S3, ? super A, P3> transferFunction3;

	private Prod3TransferFunction(final TransferFunction<S1, ? super A, P1> transferFunction1,
			final TransferFunction<S2, ? super A, P2> transferFunction2,
			final TransferFunction<S3, ? super A, P3> transferFunction3) {
		this.transferFunction1 = checkNotNull(transferFunction1);
		this.transferFunction2 = checkNotNull(transferFunction2);
		this.transferFunction3 = checkNotNull(transferFunction3);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Precision, P2 extends Precision, P3 extends Precision> Prod3TransferFunction<S1, S2, S3, A, P1, P2, P3> create(
			final TransferFunction<S1, ? super A, P1> transferFunction1,
			final TransferFunction<S2, ? super A, P2> transferFunction2,
			final TransferFunction<S3, ? super A, P3> transferFunction3) {
		return new Prod3TransferFunction<>(transferFunction1, transferFunction2, transferFunction3);
	}

	@Override
	public Collection<? extends Prod3State<S1, S2, S3>> getSuccStates(final Prod3State<S1, S2, S3> state,
			final A action, final Prod3Precision<P1, P2, P3> precision) {
		checkNotNull(state);
		checkNotNull(precision);

		final Collection<? extends S1> succStates1 = transferFunction1.getSuccStates(state._1(), action,
				precision._1());
		final Collection<? extends S2> succStates2 = transferFunction2.getSuccStates(state._2(), action,
				precision._2());
		final Collection<? extends S3> succStates3 = transferFunction3.getSuccStates(state._3(), action,
				precision._3());
		return ProdState.product(succStates1, succStates2, succStates3);
	}

}
