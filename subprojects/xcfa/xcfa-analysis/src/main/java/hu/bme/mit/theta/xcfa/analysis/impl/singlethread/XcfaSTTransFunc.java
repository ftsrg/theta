package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaSTState<S>, XcfaSTAction, XcfaSTPrec<P>> {

	private final TransFunc<S, ? super XcfaSTAction, ? super P> transFunc;

	private XcfaSTTransFunc(final TransFunc<S, ? super XcfaSTAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaSTTransFunc<S, P> create(final TransFunc<S, ? super XcfaSTAction, ? super P> transFunc) {
		return new XcfaSTTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaSTState<S>> getSuccStates(final XcfaSTState<S> state, final XcfaSTAction action, final XcfaSTPrec<P> prec) {
		final Collection<XcfaSTState<S>> newStates = new ArrayList<>();
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), action, prec.getGlobalPrec())) {
			final XcfaSTState<S> newState = state.withState(succState).withLocation(action.getTarget());
			newStates.add(newState);
		}
		return newStates;
	}
}
