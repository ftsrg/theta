package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

public final class Prod3Analysis<S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Precision, P2 extends Precision, P3 extends Precision>
		implements Analysis<Prod3State<S1, S2, S3>, A, Prod3Precision<P1, P2, P3>> {

	private final Domain<Prod3State<S1, S2, S3>> domain;
	private final InitFunction<Prod3State<S1, S2, S3>, Prod3Precision<P1, P2, P3>> initFunction;
	private final TransferFunction<Prod3State<S1, S2, S3>, A, Prod3Precision<P1, P2, P3>> transferFunction;

	private Prod3Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		checkNotNull(analysis3);
		domain = Prod3Domain.create(analysis1.getDomain(), analysis2.getDomain(), analysis3.getDomain());
		initFunction = Prod3InitFunction.create(analysis1.getInitFunction(), analysis2.getInitFunction(),
				analysis3.getInitFunction());
		transferFunction = Prod3TransferFunction.create(analysis1.getTransferFunction(),
				analysis2.getTransferFunction(), analysis3.getTransferFunction());
	}

	public static <S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Precision, P2 extends Precision, P3 extends Precision> Prod3Analysis<S1, S2, S3, A, P1, P2, P3> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3) {
		return new Prod3Analysis<>(analysis1, analysis2, analysis3);
	}

	@Override
	public Domain<Prod3State<S1, S2, S3>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<Prod3State<S1, S2, S3>, Prod3Precision<P1, P2, P3>> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<Prod3State<S1, S2, S3>, A, Prod3Precision<P1, P2, P3>> getTransferFunction() {
		return transferFunction;
	}

}
