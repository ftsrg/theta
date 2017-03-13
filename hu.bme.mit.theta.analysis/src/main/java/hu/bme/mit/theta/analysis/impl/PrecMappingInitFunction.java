package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class PrecMappingInitFunction<S extends State, PP extends Prec, PR extends Prec> implements InitFunction<S, PP> {

	private final InitFunction<S, ? super PR> initFunction;
	private final Function<? super PP, ? extends PR> mapping;

	private PrecMappingInitFunction(final InitFunction<S, ? super PR> initFunction,
			final Function<? super PP, ? extends PR> mapping) {
		this.initFunction = checkNotNull(initFunction);
		this.mapping = checkNotNull(mapping);
	}

	public static <S extends State, PP extends Prec, PR extends Prec> PrecMappingInitFunction<S, PP, PR> create(
			final InitFunction<S, ? super PR> initFunction, final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingInitFunction<>(initFunction, mapping);
	}

	@Override
	public Collection<? extends S> getInitStates(final PP prec) {
		return initFunction.getInitStates(mapping.apply(prec));
	}

}
