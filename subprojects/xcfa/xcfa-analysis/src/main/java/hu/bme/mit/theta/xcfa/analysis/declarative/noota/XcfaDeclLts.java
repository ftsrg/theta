package hu.bme.mit.theta.xcfa.analysis.declarative.noota;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaAdvanceAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaDeclAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaLabelAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaLoadAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaSequenceAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaStmtAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaStoreAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions.XcfaThreadChangeAction;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.decl.Decls.Var;

public class XcfaDeclLts implements LTS<XcfaDeclState<?>, XcfaDeclAction> {
	@Override
	public Collection<XcfaDeclAction> getEnabledActionsFor(final XcfaDeclState<?> state) {
		final Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>> currentTup4 = state.getProcesses().get(state.getCurrentProcess());
		if(currentTup4.get3().isEmpty()) {
			final Collection<XcfaDeclAction> ret = new ArrayList<>();
			for (XcfaEdge outgoingEdge : currentTup4.get1().getOutgoingEdges()) {
				ret.addAll(getActions(state, outgoingEdge, null));
			}
			if(ret.size() > 0) return ret;
		}

		for (Map.Entry<Integer, Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>>> entry : state.getProcesses().entrySet()) {
			final Integer proc = entry.getKey();
			final Tuple4<XcfaLocation, Object, Optional<VarDecl<?>>, Optional<Object>> tup4 = entry.getValue();
			if(tup4.get3().isEmpty()) {
				final XcfaThreadChangeAction threadChangeAction = XcfaThreadChangeAction.of(proc);
				final Collection<XcfaDeclAction> ret = new ArrayList<>();
				for (XcfaEdge outgoingEdge : tup4.get1().getOutgoingEdges()) {
					ret.addAll(getActions(state, outgoingEdge, threadChangeAction));
				}
				if(ret.size() > 0) return ret;
			}
		}
		return List.of();
	}

	private Collection<XcfaDeclAction> getActions(final XcfaDeclState<?> state, final XcfaEdge outgoingEdge, final XcfaThreadChangeAction threadChangeAction) {
		Collection<List<XcfaDeclAction>> actions = new ArrayList<>(List.of(new ArrayList<>(threadChangeAction == null ? List.of() : List.of(threadChangeAction))));
		final List<Stmt> stmtAction = new ArrayList<>();
		for (final XcfaLabel label : outgoingEdge.getLabels()) {
			if(label instanceof XcfaLabel.StmtXcfaLabel) {
				stmtAction.add(label.getStmt());
			} else {
				if(stmtAction.size() > 0) actions.forEach(a -> a.add(XcfaStmtAction.of(stmtAction)));
				stmtAction.clear();
				if(		label instanceof XcfaLabel.AtomicBeginXcfaLabel
					 || label instanceof XcfaLabel.AtomicEndXcfaLabel
					 || label instanceof XcfaLabel.StartThreadXcfaLabel
				     || label instanceof XcfaLabel.JoinThreadXcfaLabel
				     || label instanceof XcfaLabel.FenceXcfaLabel) {
							actions.forEach(a -> a.add(XcfaLabelAction.of(label)));
				} else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {
					final Collection<List<XcfaDeclAction>> newActions = new ArrayList<>();
					for (List<XcfaDeclAction> action : actions) {
						if(state.getStores().get(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal()) != null) {
							for (Tuple2<Object, VarDecl<?>> store : state.getStores().get(((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal())) {
								List<XcfaDeclAction> newAction = new ArrayList<>(action);
								final VarDecl<?> global = ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal();
								final VarDecl<?> ssaValue = getSingleton(Var(global.getName() + "_load_" + state.getLoadsSoFar().getOrDefault(global, 0), global.getType()));
								FrontendMetadata.create(ssaValue, "sourceGlobal", global);
								newAction.add(XcfaLoadAction.of((XcfaLabel.LoadXcfaLabel<?>) label, ssaValue, store));
								newActions.add(newAction);
							}
						}
						final VarDecl<?> global = ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal();
						final VarDecl<?> ssaValue = getSingleton(Var(global.getName() + "_load_" + state.getLoadsSoFar().getOrDefault(global, 0), global.getType()));
						FrontendMetadata.create(ssaValue, "sourceGlobal", global);
						action.add(XcfaLoadAction.of((XcfaLabel.LoadXcfaLabel<?>) label, ssaValue));
						newActions.add(action);
					}
					actions = newActions;
				} else if (label instanceof XcfaLabel.StoreXcfaLabel<?>) {
					final Collection<List<XcfaDeclAction>> newActions = new ArrayList<>();
					for (List<XcfaDeclAction> action : actions) {
						final List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> revisitableReads = state.getRevisitableLoads().get(((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal());
						int size = revisitableReads == null ? 0 : revisitableReads.size();
						for(int i = 0; i < (1 << size); ++i) {
							List<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> revisitedReads = new ArrayList<>();
							for (int i1 = 0; i1 < size; i1++) {
								if((i & (1 << i1)) > 0 ) {
									revisitedReads.add(revisitableReads.get(i1));
								}
							}
							List<XcfaDeclAction> newAction = new ArrayList<>(action);
							final VarDecl<?> global = ((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal();
							final VarDecl<?> ssaValue = getSingleton(Var(global.getName() + "_store_" + state.getStores().getOrDefault(global, List.of()).size(), global.getType()));
							FrontendMetadata.create(ssaValue, "sourceGlobal", global);
							newAction.add(XcfaStoreAction.of((XcfaLabel.StoreXcfaLabel<?>) label, ssaValue, revisitedReads));
							newActions.add(newAction);
						}
					}
					actions = newActions;
				} else throw new UnsupportedOperationException("Unknown label type: " + label);
			}
		}
		final XcfaAdvanceAction advanceAction = XcfaAdvanceAction.of(outgoingEdge.getTarget());
		if(stmtAction.size() > 0) actions.forEach(a -> a.add(XcfaStmtAction.of(stmtAction)));
		actions.forEach(a -> a.add(advanceAction));
		return actions.stream().map(XcfaSequenceAction::of).collect(Collectors.toList());
	}

	private final Map<Integer, Object> singletonStore = new HashMap<>();
	private <T> T getSingleton(T o) {
		singletonStore.putIfAbsent(o.hashCode(), o);
		//noinspection unchecked
		return (T) singletonStore.get(o.hashCode());
	}
}
