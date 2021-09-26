package hu.bme.mit.theta.xcfa.analysis.declarative;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.interleavings.XcfaAction;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclarativeTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaDeclarativeState<S>, XcfaAction, XcfaDeclarativePrec<P>> {

	private final TransFunc<S, ? super XcfaAction, ? super P> transFunc;

	private XcfaDeclarativeTransFunc(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclarativeTransFunc<S, P> create(final TransFunc<S, ? super XcfaAction, ? super P> transFunc) {
		return new XcfaDeclarativeTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaDeclarativeState<S>> getSuccStates(final XcfaDeclarativeState<S> state, final XcfaAction action, final XcfaDeclarativePrec<P> prec) {
		final List<XcfaLabel> stmts = new ArrayList<>();

		final List<XcfaLabel.StartThreadXcfaLabel> startThreadList = new ArrayList<>();
		final List<XcfaLabel.JoinThreadXcfaLabel> joinThreadList = new ArrayList<>();
		Boolean atomicBegin = null;

		for (XcfaLabel label : action.getLabels()) {
			if(label instanceof XcfaLabel.StmtXcfaLabel) {
				stmts.add(label);
			} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {
				startThreadList.add((XcfaLabel.StartThreadXcfaLabel) label);
			} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {
				joinThreadList.add((XcfaLabel.JoinThreadXcfaLabel) label);
			} else if (label instanceof XcfaLabel.AtomicBeginXcfaLabel) {
				atomicBegin = true;
			} else if (label instanceof XcfaLabel.AtomicEndXcfaLabel) {
				atomicBegin = false;
			} else if (label instanceof XcfaLabel.LoadXcfaLabel) {
				throw new UnsupportedOperationException("Could not handle label " + label);

			} else if (label instanceof XcfaLabel.StoreXcfaLabel) {
				throw new UnsupportedOperationException("Could not handle label " + label);

			} else if (label instanceof XcfaLabel.FenceXcfaLabel) {
				throw new UnsupportedOperationException("Could not handle label " + label);

			} else {
				throw new UnsupportedOperationException("Could not handle label " + label);
			}
		}

		Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
//		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), action.withLabels(stmts), prec.getGlobalPrec())) {
//			final XcfaDeclarativeState<S> newState = state.atomicbegin(action.getProcess(), atomicBegin).startthreads(startThreadList).jointhreads(action.getProcess(), joinThreadList).advance(succState, action);
//			newStates.add(newState);
//		}
		return newStates;
	}
}
