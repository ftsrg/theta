package hu.bme.mit.theta.xcfa.analysis.interleavings;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.interleavings.allinterleavings.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

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
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), action.withLabels(stmts), prec.getGlobalPrec())) {
			final XcfaState<S> newState = state.atomicbegin(action.getProcess(), atomicBegin).startthreads(startThreadList).jointhreads(action.getProcess(), joinThreadList).advance(succState, action.getProcess(), action.getTarget());
			newStates.add(newState);
		}
		return newStates;
	}
}
