package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

public final class XstsInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XstsState<S>, P> {

	private final InitFunc<S, ? super P> initFunc;

	private XstsInitFunc(final InitFunc<S, ? super P> initFunc) {
		this.initFunc = initFunc;
	}

	public static <S extends ExprState, P extends Prec> XstsInitFunc<S, P> create(final InitFunc<S, ? super P> initFunc) {
		return new XstsInitFunc<>(initFunc);
	}

	@Override
	public Collection<? extends XstsState<S>> getInitStates(final P prec) {
		final Collection<XstsState<S>> initStates = new ArrayList<>();
		for (final S subInitState : initFunc.getInitStates(prec)) {
			initStates.add(XstsState.of(subInitState, true, false));
		}
		return initStates;
	}
}
