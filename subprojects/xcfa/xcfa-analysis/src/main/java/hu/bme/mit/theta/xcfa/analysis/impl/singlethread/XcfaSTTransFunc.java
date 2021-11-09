package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTTransFunc<S extends ExprState, A extends StmtAction, P extends Prec> implements TransFunc<XcfaState<S>, A, XcfaPrec<P>> {

	private final TransFunc<S, A, P> transFunc;

	private XcfaSTTransFunc(final TransFunc<S, A, P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, A extends StmtAction, P extends Prec> XcfaSTTransFunc<S, A, P> create(final TransFunc<S, A, P> transFunc) {
		return new XcfaSTTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaState<S>> getSuccStates(final XcfaState<S> inState, final A inAction, final XcfaPrec<P> prec) {
		XcfaSTState<S> state = (XcfaSTState<S>) inState;
		XcfaSTAction action = (XcfaSTAction) inAction;
		final Collection<XcfaState<S>> newStates = new ArrayList<>();
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), inAction, prec.getGlobalPrec())) {
			final XcfaState<S> newState = state.withState(succState).withLocation(action.getTarget());
			newStates.add(newState);
		}
		return newStates;
	}
}
