package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;

final class PrecMappingTransferFunc<S extends State, A extends Action, PP extends Prec, PR extends Prec>
		implements TransferFunc<S, A, PP> {

	private final TransferFunc<S, ? super A, ? super PR> transferFunc;
	private final Function<? super PP, ? extends PR> mapping;

	private PrecMappingTransferFunc(final TransferFunc<S, ? super A, ? super PR> transferFunc,
			final Function<? super PP, ? extends PR> mapping) {
		this.transferFunc = checkNotNull(transferFunc);
		this.mapping = checkNotNull(mapping);
	}

	public static <S extends State, A extends Action, PP extends Prec, PR extends Prec> PrecMappingTransferFunc<S, A, PP, PR> create(
			final TransferFunc<S, ? super A, ? super PR> transferFunc,
			final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingTransferFunc<>(transferFunc, mapping);
	}

	@Override
	public Collection<? extends S> getSuccStates(final S state, final A action, final PP prec) {
		return transferFunc.getSuccStates(state, action, mapping.apply(prec));
	}

}
