package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaTransFunc<S extends ExprState, A extends StmtAction, P extends Prec> implements TransFunc<hu.bme.mit.theta.xcfa.analysis.common.XcfaState<S>, A, XcfaPrec<P>> {

	private final TransFunc<S, A, ? super P> transFunc;

	private XcfaTransFunc(final TransFunc<S, A, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, A extends StmtAction, P extends Prec> XcfaTransFunc<S, A, P> create(final TransFunc<S, A, ? super P> transFunc) {
		return new XcfaTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaState<S>> getSuccStates(final hu.bme.mit.theta.xcfa.analysis.common.XcfaState<S> commonState, final A commonAction, final XcfaPrec<P> prec) {
		XcfaState<S> state = (XcfaState<S>) commonState;
		hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaAction action = (hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaAction) commonAction;

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

		Collection<XcfaState<S>> newStates = new ArrayList<>();
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), (A) action.withLabels(stmts), prec.getGlobalPrec())) {
			final XcfaState<S> newState = state.atomicbegin(action.getProcess(), atomicBegin).startthreads(startThreadList).jointhreads(action.getProcess(), joinThreadList).advance(succState, action);
			newStates.add(newState);
		}
		return newStates;
	}
}
