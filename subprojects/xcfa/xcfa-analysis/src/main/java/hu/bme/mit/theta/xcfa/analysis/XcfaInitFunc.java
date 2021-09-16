package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

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
		final Map<Integer, ? extends Collection<? extends S>> initStates = initLocs.keySet().stream().map(xcfaLocation -> Map.entry(xcfaLocation, initFunc.getInitStates(prec.getPrec(xcfaLocation)))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		checkState(initStates.values().stream().allMatch(s -> s.size() == 1), "Currently cannot handle nondeterministic starting state!");
		final Map<Integer, ? extends S> processStates = initStates.entrySet().stream().map(e -> Map.entry(e.getKey(), e.getValue().iterator().next())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		final Map<Integer, XcfaProcessState<S>> stateMap = initLocs.entrySet().stream().map(e -> Map.entry(e.getKey(), (XcfaProcessState<S>)XcfaProcessState.create(processStates.get(e.getKey()), e.getValue()))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		final Collection<? extends S> globalInitStates = initFunc.getInitStates(prec.getGlobalPrec());
		checkState(globalInitStates.size() == 1, "Currently cannot handle nondeterministic starting state!");
		final XcfaState<S> xcfaState = XcfaState.create(stateMap, initLocs.keySet(), globalInitStates.iterator().next());
		return Set.of(xcfaState);
	}
}
