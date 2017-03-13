package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

final class PrecMappingTransferFunction<S extends State, A extends Action, PP extends Prec, PR extends Prec>
		implements TransferFunction<S, A, PP> {

	private final TransferFunction<S, ? super A, ? super PR> transferFunction;
	private final Function<? super PP, ? extends PR> mapping;

	private PrecMappingTransferFunction(final TransferFunction<S, ? super A, ? super PR> transferFunction,
			final Function<? super PP, ? extends PR> mapping) {
		this.transferFunction = checkNotNull(transferFunction);
		this.mapping = checkNotNull(mapping);
	}

	public static <S extends State, A extends Action, PP extends Prec, PR extends Prec> PrecMappingTransferFunction<S, A, PP, PR> create(
			final TransferFunction<S, ? super A, ? super PR> transferFunction,
			final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingTransferFunction<>(transferFunction, mapping);
	}

	@Override
	public Collection<? extends S> getSuccStates(final S state, final A action, final PP prec) {
		return transferFunction.getSuccStates(state, action, mapping.apply(prec));
	}

}
