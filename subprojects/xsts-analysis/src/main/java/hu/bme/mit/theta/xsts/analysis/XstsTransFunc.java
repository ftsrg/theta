package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XstsTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XstsState<S>, XstsAction, P> {

	private final TransFunc<S, ? super XstsAction, ? super P> transFunc;

	private XstsTransFunc(final TransFunc<S, ? super XstsAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XstsTransFunc<S, P> create(
			final TransFunc<S, ? super XstsAction, ? super P> transFunc) {
		return new XstsTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XstsState<S>> getSuccStates(final XstsState<S> state, final XstsAction action, final P prec) {

		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final Collection<XstsState<S>> succStates = new ArrayList<>();
		final S subState = state.getState();
		final boolean succWasLastEnv = !state.lastActionWasEnv();

		final Collection<? extends S> subSuccStates = transFunc.getSuccStates(subState, action, prec);
		for (final S subSuccState : subSuccStates) {
			final XstsState<S> succState = XstsState.of(subSuccState, succWasLastEnv, true);
			succStates.add(succState);
		}
		return succStates;
	}
}
