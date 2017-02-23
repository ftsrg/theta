package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class FixedPrecInitFunction<S extends State, P extends Prec> implements InitFunction<S, NullPrec> {

	private final InitFunction<S, P> initFunction;
	private final P fixedPrec;

	private FixedPrecInitFunction(final InitFunction<S, P> initFunction, final P prec) {
		this.initFunction = checkNotNull(initFunction);
		this.fixedPrec = checkNotNull(prec);
	}

	public static <S extends State, P extends Prec> FixedPrecInitFunction<S, P> create(
			final InitFunction<S, P> initFunction, final P prec) {
		return new FixedPrecInitFunction<>(initFunction, prec);
	}

	@Override
	public Collection<? extends S> getInitStates(final NullPrec prec) {
		checkNotNull(prec);
		return initFunction.getInitStates(fixedPrec);
	}

}
