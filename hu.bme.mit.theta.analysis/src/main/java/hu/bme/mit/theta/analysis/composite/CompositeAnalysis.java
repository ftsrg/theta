package hu.bme.mit.theta.analysis.composite;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

public final class CompositeAnalysis<S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision>
		implements Analysis<CompositeState<S1, S2>, A, CompositePrecision<P1, P2>> {

	private final Analysis<S1, A, P1> analysis1;
	private final Analysis<S2, A, P2> analysis2;

	private final Domain<CompositeState<S1, S2>> domain;
	private final InitFunction<CompositeState<S1, S2>, CompositePrecision<P1, P2>> initFunction;
	private final TransferFunction<CompositeState<S1, S2>, A, CompositePrecision<P1, P2>> transferFunction;

	private volatile ActionFunction<? super CompositeState<S1, S2>, ? extends A> actionFunction = null;

	private CompositeAnalysis(final Analysis<S1, A, P1> analysis1, final Analysis<S2, A, P2> analysis2) {
		this.analysis1 = checkNotNull(analysis1);
		this.analysis2 = checkNotNull(analysis2);
		domain = CompositeDomain.create(analysis1.getDomain(), analysis2.getDomain());
		initFunction = new CompositeInitFunction<>(analysis1.getInitFunction(), analysis2.getInitFunction());
		transferFunction = new CompositeTransferFunction<>(analysis1.getTransferFunction(),
				analysis2.getTransferFunction());
	}

	public static <S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision> CompositeAnalysis<S1, S2, A, P1, P2> create(
			final Analysis<S1, A, P1> analysis1, final Analysis<S2, A, P2> analysis2) {
		return new CompositeAnalysis<>(analysis1, analysis2);
	}

	@Override
	public Domain<CompositeState<S1, S2>> getDomain() {
		return domain;
	}

	@Override
	public InitFunction<CompositeState<S1, S2>, CompositePrecision<P1, P2>> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<CompositeState<S1, S2>, A, CompositePrecision<P1, P2>> getTransferFunction() {
		return transferFunction;
	}

	@Override
	public ActionFunction<? super CompositeState<S1, S2>, ? extends A> getActionFunction() {
		ActionFunction<? super CompositeState<S1, S2>, ? extends A> result = actionFunction;
		if (result == null) {
			result = new CompositeActionFunction<>(analysis1.getActionFunction(), analysis2.getActionFunction());
			actionFunction = result;
		}
		return result;
	}

}
