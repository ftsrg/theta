package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

public final class Prod2Analysis<S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision>
		implements Analysis<Prod2State<S1, S2>, A, Prod2Precision<P1, P2>> {

	private final Domain<Prod2State<S1, S2>> domain;
	private final InitFunction<Prod2State<S1, S2>, Prod2Precision<P1, P2>> initFunction;
	private final TransferFunction<Prod2State<S1, S2>, A, Prod2Precision<P1, P2>> transferFunction;

	private Prod2Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		domain = Prod2Domain.create(analysis1.getDomain(), analysis2.getDomain());
		initFunction = Prod2InitFunction.create(analysis1.getInitFunction(), analysis2.getInitFunction());
		transferFunction = Prod2TransferFunction.create(analysis1.getTransferFunction(),
				analysis2.getTransferFunction());
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision> Prod2Analysis<S1, S2, A, P1, P2> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2) {
		return new Prod2Analysis<>(analysis1, analysis2);
	}

	@Override
	public Domain<Prod2State<S1, S2>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<Prod2State<S1, S2>, Prod2Precision<P1, P2>> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<Prod2State<S1, S2>, A, Prod2Precision<P1, P2>> getTransferFunction() {
		return transferFunction;
	}

}
