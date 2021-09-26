package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclarativeInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XcfaDeclarativeState<S>, XcfaDeclarativePrec<P>> {
	private final List<XcfaLocation> initLocs;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaDeclarativeInitFunc(final List<XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		this.initLocs = checkNotNull(initLocs);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclarativeInitFunc<S, P> create(final List<XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		return new XcfaDeclarativeInitFunc<>(initLocs, initFunc);
	}

	@Override
	public Collection<XcfaDeclarativeState<S>> getInitStates(final XcfaDeclarativePrec<P> prec) {
		final Collection<XcfaDeclarativeState<S>> set = new ArrayList<>();
		for (S s : initFunc.getInitStates(prec.getGlobalPrec())) {
//			final XcfaDeclarativeState<S> xcfaState = XcfaDeclarativeState.create(initLocs.stream().map(xcfaLocation -> Map.entry(xcfaLocation, true)).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)), s);
//			set.add(xcfaState);
		}
		return set;
	}
}
