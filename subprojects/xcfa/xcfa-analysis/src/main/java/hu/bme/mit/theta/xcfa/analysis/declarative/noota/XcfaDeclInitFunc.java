package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.cat.solver.MemoryModel;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.prec.XcfaDeclPrec;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XcfaDeclState<S>, XcfaDeclPrec<P>> {
	private final XcfaLocation initLoc;
	private final MemoryModel memoryModel;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaDeclInitFunc(final XcfaLocation initLoc, final MemoryModel memoryModel, final InitFunc<S, ? super P> initFunc) {
		this.initLoc = checkNotNull(initLoc);
		this.memoryModel = memoryModel;
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclInitFunc<S, P> create(
			final XcfaLocation initLoc, final MemoryModel memoryModel, final InitFunc<S, ? super P> initFunc) {
		return new XcfaDeclInitFunc<>(initLoc, memoryModel, initFunc);
	}

	@Override
	public Collection<XcfaDeclState<S>> getInitStates(final XcfaDeclPrec<P> prec) {
		final Collection<XcfaDeclState<S>> set = new ArrayList<>();
		for (S s : initFunc.getInitStates(prec.getGlobalPrec())) {
			final XcfaDeclState<S> xcfaState = XcfaDeclState.init(initLoc, memoryModel, s);
			set.add(xcfaState);
		}
		return set;
	}
}
