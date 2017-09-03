package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

final class CfaInitFunc<S extends ExprState, P extends Prec> implements InitFunc<CfaState<S>, CfaPrec<P>> {

	private final Loc initLoc;
	private final InitFunc<S, ? super P> initFunc;

	private CfaInitFunc(final Loc initLoc, final InitFunc<S, ? super P> initFunc) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> CfaInitFunc<S, P> create(final Loc initLoc,
			final InitFunc<S, ? super P> initFunc) {
		return new CfaInitFunc<>(initLoc, initFunc);
	}

	@Override
	public Collection<CfaState<S>> getInitStates(final CfaPrec<P> prec) {
		checkNotNull(prec);

		final Collection<CfaState<S>> initStates = new ArrayList<>();
		final P subPrec = prec.getPrec(initLoc);
		final Collection<? extends S> subInitStates = initFunc.getInitStates(subPrec);
		for (final S subInitState : subInitStates) {
			final CfaState<S> initState = CfaState.of(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
