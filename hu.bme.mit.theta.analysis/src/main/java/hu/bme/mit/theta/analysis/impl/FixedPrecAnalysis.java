package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

public final class FixedPrecAnalysis<S extends State, A extends Action, P extends Prec>
		implements Analysis<S, A, NullPrec> {

	private final Analysis<S, A, P> analysis;

	private final InitFunction<S, NullPrec> initFunction;
	private final TransferFunction<S, A, NullPrec> transferFunction;

	private FixedPrecAnalysis(final Analysis<S, A, P> analysis, final P precision) {
		this.analysis = checkNotNull(analysis);
		initFunction = FixedPrecInitFunction.create(analysis.getInitFunction(), precision);
		transferFunction = FixedPrecTransferFunction.create(analysis.getTransferFunction(), precision);
	}

	public static <S extends State, A extends Action, P extends Prec> FixedPrecAnalysis<S, A, P> create(
			final Analysis<S, A, P> analysis, final P precision) {
		return new FixedPrecAnalysis<>(analysis, precision);
	}

	@Override
	public Domain<S> getDomain() {
		return analysis.getDomain();
	}

	@Override
	public InitFunction<S, NullPrec> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<S, A, NullPrec> getTransferFunction() {
		return transferFunction;
	}

}
