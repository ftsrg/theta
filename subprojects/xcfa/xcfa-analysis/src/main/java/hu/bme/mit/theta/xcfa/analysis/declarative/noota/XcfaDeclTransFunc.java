package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaAdvanceAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaDeclAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaLabelAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaLoadAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaSequenceAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaStmtAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaStoreAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaThreadChangeAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.prec.XcfaDeclPrec;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaDeclTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaDeclState<S>, XcfaDeclAction, XcfaDeclPrec<P>> {

	private final TransFunc<S, ? super XcfaDeclAction, ? super P> transFunc;

	private XcfaDeclTransFunc(final TransFunc<S, ? super XcfaDeclAction, ? super P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaDeclTransFunc<S, P> create(final TransFunc<S, ? super XcfaDeclAction, ? super P> transFunc) {
		return new XcfaDeclTransFunc<>(transFunc);
	}

	@Override
	public Collection<XcfaDeclState<S>> getSuccStates(XcfaDeclState<S> state, XcfaDeclAction action, XcfaDeclPrec<P> prec) {
		if(action instanceof XcfaSequenceAction) {
			Collection<XcfaDeclState<S>> states = List.of(state);
			for (XcfaDeclAction xcfaDeclAction : ((XcfaSequenceAction) action).getActions()) {
				final Collection<XcfaDeclState<S>> newStates = new ArrayList<>();
				for (XcfaDeclState<S> st : states) {
					newStates.addAll(getSuccStates(st, xcfaDeclAction, prec));
				}
				states = newStates;
			}
			return states;
		} else if (action instanceof XcfaThreadChangeAction) {
			return List.of(state.changeThread(((XcfaThreadChangeAction) action).getProcess()));
		} else if (action instanceof XcfaAdvanceAction) {
			return List.of(state.advance(((XcfaAdvanceAction) action).getTarget()));
		} else if (action instanceof XcfaStmtAction) {
			return transFunc.getSuccStates(state.getState(), action, prec.getGlobalPrec()).stream().map(state::newState).collect(Collectors.toList());
		} else if (action instanceof XcfaLabelAction) {
			final XcfaLabel label = ((XcfaLabelAction) action).getLabel();
			if(label instanceof XcfaLabel.AtomicBeginXcfaLabel) {
				return List.of(state.atomicBegin());
			} else if (label instanceof XcfaLabel.AtomicEndXcfaLabel) {
				return List.of(state.atomicEnd());
			} else if (label instanceof XcfaLabel.StartThreadXcfaLabel) {
				return List.of(state.startThread((XcfaLabel.StartThreadXcfaLabel) label));
			} else if (label instanceof XcfaLabel.JoinThreadXcfaLabel) {
				return List.of(state.joinThread((XcfaLabel.JoinThreadXcfaLabel) label));
			} else if (label instanceof XcfaLabel.FenceXcfaLabel) {
				return List.of(state.addFence((XcfaLabel.FenceXcfaLabel) label));
			} else throw new UnsupportedOperationException("Label type not known: " + action);
		} else if (action instanceof XcfaLoadAction) {
			if(prec.getTrackedVariables().contains(((XcfaLoadAction) action).getLoad().getGlobal())) {
				final List<XcfaDeclState<S>> collect = transFunc.getSuccStates(state.getState(), action, prec.getGlobalPrec()).stream().
						map(newState -> state.newState(newState).
								addRead(((XcfaLoadAction) action).getLoad(), ((XcfaLoadAction) action).getUniqeObject(),
										((XcfaLoadAction) action).getReadingFrom().map(Tuple2::get1).orElse(null))).collect(Collectors.toList());
				return collect;
			} else {
				return List.of(state);
			}
		} else if (action instanceof XcfaStoreAction) {
			if(prec.getTrackedVariables().contains(((XcfaStoreAction) action).getStore().getGlobal())) {
				final List<XcfaDeclState<S>> collect = transFunc.getSuccStates(state.getState(), action, prec.getGlobalPrec()).stream().
						map(newState -> state.newState(newState).
								addStore(((XcfaStoreAction) action).getStore(), ((XcfaStoreAction) action).getUniqeObject(), ((XcfaStoreAction) action).getSsaValue(),
										((XcfaStoreAction) action).getWritingTo())).collect(Collectors.toList());
				return collect;
			} else {
				return List.of(state);
			}
		}
		else throw new UnsupportedOperationException("Action type not known: " + action);
	}
}
