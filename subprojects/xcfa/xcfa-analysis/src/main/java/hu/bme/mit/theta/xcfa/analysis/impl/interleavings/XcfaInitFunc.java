package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XcfaState<S>, XcfaPrec<P>> {
	private final List<XcfaLocation> initLocs;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaInitFunc(final List<XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		this.initLocs = checkNotNull(initLocs);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaInitFunc<S, P> create(final List<XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		return new XcfaInitFunc<>(initLocs, initFunc);
	}

	@Override
	public Collection<XcfaState<S>> getInitStates(final XcfaPrec<P> prec) {
		final Collection<XcfaState<S>> set = new ArrayList<>();
		for (S s : initFunc.getInitStates(prec.getGlobalPrec())) {
			final XcfaState<S> xcfaState = hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaState.create(initLocs.stream().map(xcfaLocation -> Map.entry(xcfaLocation, true)).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)), s);
			set.add(xcfaState);
		}
		return set;
	}
}
