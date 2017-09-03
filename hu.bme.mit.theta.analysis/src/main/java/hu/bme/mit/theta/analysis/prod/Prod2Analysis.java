package hu.bme.mit.theta.analysis.prod;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;

public final class Prod2Analysis<S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec>
		implements Analysis<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> {

	private final Domain<Prod2State<S1, S2>> domain;
	private final InitFunc<Prod2State<S1, S2>, Prod2Prec<P1, P2>> initFunc;
	private final TransferFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> transferFunc;

	private Prod2Analysis(final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2) {
		checkNotNull(analysis1);
		checkNotNull(analysis2);
		domain = Prod2Domain.create(analysis1.getDomain(), analysis2.getDomain());
		initFunc = Prod2InitFunc.create(analysis1.getInitFunc(), analysis2.getInitFunc());
		transferFunc = Prod2TransferFunc.create(analysis1.getTransferFunc(), analysis2.getTransferFunc());
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Prec, P2 extends Prec> Prod2Analysis<S1, S2, A, P1, P2> create(
			final Analysis<S1, ? super A, P1> analysis1, final Analysis<S2, ? super A, P2> analysis2) {
		return new Prod2Analysis<>(analysis1, analysis2);
	}

	@Override
	public Domain<Prod2State<S1, S2>> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<Prod2State<S1, S2>, Prod2Prec<P1, P2>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<Prod2State<S1, S2>, A, Prod2Prec<P1, P2>> getTransferFunc() {
		return transferFunc;
	}

}
