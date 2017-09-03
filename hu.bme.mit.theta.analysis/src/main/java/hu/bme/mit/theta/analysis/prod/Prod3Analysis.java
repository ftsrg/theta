package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;

public final class Prod3Analysis<S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec>
		implements Analysis<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> {

	private final Domain<Prod3State<S1, S2, S3>> domain;
	private final InitFunc<Prod3State<S1, S2, S3>, Prod3Prec<P1, P2, P3>> initFunc;
	private final TransferFunc<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> transferFunc;

	private Prod3Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		checkNotNull(analysis3);
		domain = Prod3Domain.create(analysis1.getDomain(), analysis2.getDomain(), analysis3.getDomain());
		initFunc = Prod3InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc(), analysis3.getInitFunc());
		transferFunc = Prod3TransferFunc.create(analysis1.getTransferFunc(), analysis2.getTransferFunc(),
				analysis3.getTransferFunc());
	}

	public static <S1 extends State, S2 extends State, S3 extends State, A extends Action, P1 extends Prec, P2 extends Prec, P3 extends Prec> Prod3Analysis<S1, S2, S3, A, P1, P2, P3> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2,
			final Analysis<S3, ? super A, P3> analysis3) {
		return new Prod3Analysis<>(analysis1, analysis2, analysis3);
	}

	@Override
	public Domain<Prod3State<S1, S2, S3>> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<Prod3State<S1, S2, S3>, Prod3Prec<P1, P2, P3>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<Prod3State<S1, S2, S3>, A, Prod3Prec<P1, P2, P3>> getTransferFunc() {
		return transferFunc;
	}

}
