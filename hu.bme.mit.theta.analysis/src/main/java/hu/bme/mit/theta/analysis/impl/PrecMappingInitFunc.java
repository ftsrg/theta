package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class PrecMappingInitFunc<S extends State, PP extends Prec, PR extends Prec> implements InitFunc<S, PP> {

	private final InitFunc<S, ? super PR> initFunc;
	private final Function<? super PP, ? extends PR> mapping;

	private PrecMappingInitFunc(final InitFunc<S, ? super PR> initFunc,
			final Function<? super PP, ? extends PR> mapping) {
		this.initFunc = checkNotNull(initFunc);
		this.mapping = checkNotNull(mapping);
	}

	public static <S extends State, PP extends Prec, PR extends Prec> PrecMappingInitFunc<S, PP, PR> create(
			final InitFunc<S, ? super PR> initFunc, final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingInitFunc<>(initFunc, mapping);
	}

	@Override
	public Collection<? extends S> getInitStates(final PP prec) {
		return initFunc.getInitStates(mapping.apply(prec));
	}

}
