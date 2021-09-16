package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class XcfaTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaState<S>, XcfaAction, XcfaPrec<P>> {

	private final TransFunc<S, ? super XcfaAction, ? super P> transFunc;

	private XcfaTransFunc(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaTransFunc<S, P> create(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		return new XcfaTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaState<S>> getSuccStates(final XcfaState<S> state, final XcfaAction action, final XcfaPrec<P> prec) {
		checkState(state.getEnabledProcesses().contains(action.getProcess()), "Non-enabled process chosen!");
		Collection<XcfaState<S>> newStates = new ArrayList<>();
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), action, prec.getGlobalPrec())) {
			final XcfaState<S> newState = state.advance(succState, action.getProcess(), action.getTarget());
			newStates.add(newState);
		}
		return newStates;
	}
}
