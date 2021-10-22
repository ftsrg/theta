package hu.bme.mit.theta.xcfa.analysis.declarative.oota;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class XcfaDeclarativeTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaDeclarativeState<S>, XcfaDeclarativeAction, XcfaDeclarativePrec<P>> {

	private final TransFunc<S, ? super XcfaDeclarativeAction, ? super P> transFunc;

	private XcfaDeclarativeTransFunc(final TransFunc<S, ? super XcfaDeclarativeAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclarativeTransFunc<S, P> create(final TransFunc<S, ? super XcfaDeclarativeAction, ? super P> transFunc) {
		return new XcfaDeclarativeTransFunc<>(transFunc);
	}

	@Override
	public Collection<? extends XcfaDeclarativeState<S>> getSuccStates(XcfaDeclarativeState<S> state, final XcfaDeclarativeAction action, final XcfaDeclarativePrec<P> prec) {
		final List<XcfaLabel> stmts = new ArrayList<>();

		Collection<XcfaDeclarativeState<S>> states = List.of(state);

		for (XcfaLabel label : action.getLabels()) {
			if(label instanceof XcfaLabel.StmtXcfaLabel) {
				stmts.add(label);
			} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {
				Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
				for (XcfaDeclarativeState<S> sXcfaDeclarativeState : states) {
					newStates.add(sXcfaDeclarativeState.startthreads((XcfaLabel.StartThreadXcfaLabel) label));
				}
				states = newStates;
			} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {
				Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
				for (XcfaDeclarativeState<S> sXcfaDeclarativeState : states) {
					newStates.add(sXcfaDeclarativeState.jointhreads((XcfaLabel.JoinThreadXcfaLabel) label));
				}
				states = newStates;
			} else if (label instanceof XcfaLabel.AtomicBeginXcfaLabel) {
				throw new UnsupportedOperationException("Not yet implemented");
			} else if (label instanceof XcfaLabel.AtomicEndXcfaLabel) {
				throw new UnsupportedOperationException("Not yet implemented");
			} else if (label instanceof XcfaLabel.LoadXcfaLabel) {
				if(prec.getTrackedGlobalVars().contains(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal())) {
					Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
					for (XcfaDeclarativeState<S> sXcfaDeclarativeState : states) {
						final Collection<XcfaDeclarativeState<S>> readStates = sXcfaDeclarativeState.read((XcfaLabel.LoadXcfaLabel<?>) label);
						newStates.addAll(readStates);
					}
					states = newStates;
				}
				stmts.add(Stmt(Havoc(((XcfaLabel.LoadXcfaLabel<?>) label).getLocal())));
			} else if (label instanceof XcfaLabel.StoreXcfaLabel) {
				if(prec.getTrackedGlobalVars().contains(((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal())) {
					Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
					for (XcfaDeclarativeState<S> sXcfaDeclarativeState : states) {
						final Collection<XcfaDeclarativeState<S>> readStates = sXcfaDeclarativeState.write((XcfaLabel.StoreXcfaLabel<?>) label);
						newStates.addAll(readStates);
					}
					states = newStates;
				}
			} else if (label instanceof XcfaLabel.FenceXcfaLabel) {
				throw new UnsupportedOperationException("Not yet implemented!");
			} else {
				throw new UnsupportedOperationException("Could not handle label " + label);
			}
		}
		Collection<XcfaDeclarativeState<S>> newStates = new ArrayList<>();
		for (final S succState : transFunc.getSuccStates(state.getState(), action.withLabels(stmts), prec.getGlobalPrec())) {
			for (XcfaDeclarativeState<S> sXcfaDeclarativeState : states) {
				newStates.add(sXcfaDeclarativeState.advance(succState, action));
			}
		}
		return newStates;
	}
}
