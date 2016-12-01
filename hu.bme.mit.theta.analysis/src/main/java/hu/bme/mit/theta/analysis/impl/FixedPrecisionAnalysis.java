package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

public final class FixedPrecisionAnalysis<S extends State, A extends Action, P extends Precision>
		implements Analysis<S, A, NullPrecision> {

	private final Analysis<S, A, P> analysis;

	private final InitFunction<S, NullPrecision> initFunction;
	private final TransferFunction<S, A, NullPrecision> transferFunction;

	private FixedPrecisionAnalysis(final Analysis<S, A, P> analysis, final P precision) {
		this.analysis = checkNotNull(analysis);
		initFunction = FixedPrecisionInitFunction.create(analysis.getInitFunction(), precision);
		transferFunction = FixedPrecisionTransferFunction.create(analysis.getTransferFunction(), precision);
	}

	public static <S extends State, A extends Action, P extends Precision> FixedPrecisionAnalysis<S, A, P> create(
			final Analysis<S, A, P> analysis, final P precision) {
		return new FixedPrecisionAnalysis<>(analysis, precision);
	}

	@Override
	public Domain<S> getDomain() {
		return analysis.getDomain();
	}

	@Override
	public InitFunction<S, NullPrecision> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<S, A, NullPrecision> getTransferFunction() {
		return transferFunction;
	}

}
