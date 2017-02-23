package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class FixedPrecInitFunction<S extends State, P extends Prec> implements InitFunction<S, NullPrec> {

	private final InitFunction<S, P> initFunction;
	private final P fixedPrecision;

	private FixedPrecInitFunction(final InitFunction<S, P> initFunction, final P precision) {
		this.initFunction = checkNotNull(initFunction);
		this.fixedPrecision = checkNotNull(precision);
	}

	public static <S extends State, P extends Prec> FixedPrecInitFunction<S, P> create(
			final InitFunction<S, P> initFunction, final P precision) {
		return new FixedPrecInitFunction<>(initFunction, precision);
	}

	@Override
	public Collection<? extends S> getInitStates(final NullPrec precision) {
		checkNotNull(precision);
		return initFunction.getInitStates(fixedPrecision);
	}

}
