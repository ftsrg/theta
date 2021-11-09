package hu.bme.mit.theta.xcfa.analysis.impl.declarative;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclarativeInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XcfaDeclarativeState<S>, XcfaDeclarativePrec<P>> {
	private final XcfaLocation initLoc;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaDeclarativeInitFunc(final XcfaLocation initLoc, final InitFunc<S, ? super P> initFunc) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclarativeInitFunc<S, P> create(final XcfaLocation initLoc, final InitFunc<S, ? super P> initFunc) {
		return new XcfaDeclarativeInitFunc<>(initLoc, initFunc);
	}

	@Override
	public Collection<XcfaDeclarativeState<S>> getInitStates(final XcfaDeclarativePrec<P> prec) {
		final Collection<XcfaDeclarativeState<S>> set = new ArrayList<>();
		for (S s : initFunc.getInitStates(prec.getGlobalPrec())) {
			final XcfaDeclarativeState<S> xcfaState = XcfaDeclarativeState.create(initLoc, s);
			set.add(xcfaState);
		}
		return set;
	}
}
