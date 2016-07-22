package hu.bme.mit.inf.ttmc.analysis.composite;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;

public class CompositeAnalysis<S1 extends State, S2 extends State, A extends Action, P1 extends Precision, P2 extends Precision>
		implements Analysis<CompositeState<S1, S2>, A, CompositePrecision<P1, P2>> {

	private final Domain<CompositeState<S1, S2>> domain;
	private final InitFunction<CompositeState<S1, S2>, CompositePrecision<P1, P2>> initFunction;
	private final TransferFunction<CompositeState<S1, S2>, A, CompositePrecision<P1, P2>> transferFunction;

	public CompositeAnalysis(final Analysis<S1, A, P1> analysis1, final Analysis<S2, A, P2> analysis2) {
		domain = new CompositeDomain<>(analysis1.getDomain(), analysis2.getDomain());
		initFunction = new CompositeInitFunction<>(analysis1.getInitFunction(), analysis2.getInitFunction());
		transferFunction = new CompositeTransferFunction<>(analysis1.getTransferFunction(),
				analysis2.getTransferFunction());
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

}
