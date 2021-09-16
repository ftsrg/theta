package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Collection;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XcfaState<S>, XcfaPrec<P>> {
	private final Map<Integer, XcfaLocation> initLocs;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaInitFunc(final Map<Integer, XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		this.initLocs = checkNotNull(initLocs);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaInitFunc<S, P> create(final Map<Integer, XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		return new XcfaInitFunc<>(initLocs, initFunc);
	}

	@Override
	public Collection<? extends XcfaState<S>> getInitStates(final XcfaPrec<P> prec) {
		return null;
	}
}
