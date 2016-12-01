package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

final class FixedPrecisionTransferFunction<S extends State, A extends Action, P extends Precision>
		implements TransferFunction<S, A, NullPrecision> {

	final TransferFunction<S, A, P> transferFunction;
	final P fixedPrecision;

	private FixedPrecisionTransferFunction(final TransferFunction<S, A, P> transferFunction, final P precision) {
		this.transferFunction = checkNotNull(transferFunction);
		this.fixedPrecision = checkNotNull(precision);
	}

	public static <S extends State, A extends Action, P extends Precision> FixedPrecisionTransferFunction<S, A, P> create(
			final TransferFunction<S, A, P> transferFunction, final P precision) {
		return new FixedPrecisionTransferFunction<>(transferFunction, precision);
	}

	@Override
	public Collection<? extends S> getSuccStates(final S state, final A action, final NullPrecision precision) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(precision);
		return transferFunction.getSuccStates(state, action, fixedPrecision);
	}

}
