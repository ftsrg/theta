package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

final class Prod3TransferFunction<S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec>
		implements TransferFunction<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> {

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

	public static <S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3TransferFunction<S1, S2, S3, A, P1, P2, P3> create(
			final TransferFunction<S1, ? super A, P1> transferFunction1,
			final TransferFunction<S2, ? super A, P2> transferFunction2,
			final TransferFunction<S3, ? super A, P3> transferFunction3) {
		return new Prod3TransferFunction<>(transferFunction1, transferFunction2, transferFunction3);
	}

	@Override
	public Collection<? extends Prod3State<S1, S2, S3>> getSuccStates(final Prod3State<S1, S2, S3> state,
			final A action, final Prod3Prec<P1, P2, P3> prec) {
		checkNotNull(state);
		checkNotNull(prec);

		final Collection<? extends S1> succStates1 = transferFunction1.getSuccStates(state._1(), action,
				prec._1());
		final Collection<? extends S2> succStates2 = transferFunction2.getSuccStates(state._2(), action,
				prec._2());
		final Collection<? extends S3> succStates3 = transferFunction3.getSuccStates(state._3(), action,
				prec._3());
		return ProdState.product(succStates1, succStates2, succStates3);
	}

}
