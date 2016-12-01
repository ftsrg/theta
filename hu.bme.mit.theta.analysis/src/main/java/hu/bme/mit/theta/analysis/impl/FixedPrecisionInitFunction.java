package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

final class FixedPrecisionInitFunction<S extends State, P extends Precision> implements InitFunction<S, NullPrecision> {

	private final InitFunction<S, P> initFunction;
	private final P fixedPrecision;

	private FixedPrecisionInitFunction(final InitFunction<S, P> initFunction, final P precision) {
		this.initFunction = checkNotNull(initFunction);
		this.fixedPrecision = checkNotNull(precision);
	}

	public static <S extends State, P extends Precision> FixedPrecisionInitFunction<S, P> create(
			final InitFunction<S, P> initFunction, final P precision) {
		return new FixedPrecisionInitFunction<>(initFunction, precision);
	}

	@Override
	public Collection<? extends S> getInitStates(final NullPrecision precision) {
		checkNotNull(precision);
		return initFunction.getInitStates(fixedPrecision);
	}

}
