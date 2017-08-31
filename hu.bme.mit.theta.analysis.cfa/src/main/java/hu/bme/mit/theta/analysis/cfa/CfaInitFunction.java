package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

final class CfaInitFunction<S extends ExprState, P extends Prec> implements InitFunction<CfaState<S>, CfaPrec<P>> {

	private final Loc initLoc;
	private final InitFunction<S, ? super P> initFunction;

	private CfaInitFunction(final Loc initLoc, final InitFunction<S, ? super P> initFunction) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunction = checkNotNull(initFunction);
	}

	public static <S extends ExprState, P extends Prec> CfaInitFunction<S, P> create(final Loc initLoc,
			final InitFunction<S, ? super P> initFunction) {
		return new CfaInitFunction<>(initLoc, initFunction);
	}

	@Override
	public Collection<CfaState<S>> getInitStates(final CfaPrec<P> prec) {
		checkNotNull(prec);

		final Collection<CfaState<S>> initStates = new ArrayList<>();
		final P subPrec = prec.getPrec(initLoc);
		final Collection<? extends S> subInitStates = initFunction.getInitStates(subPrec);
		for (final S subInitState : subInitStates) {
			final CfaState<S> initState = CfaState.of(initLoc, subInitState);
			initStates.add(initState);
		}
		return initStates;
	}

}
