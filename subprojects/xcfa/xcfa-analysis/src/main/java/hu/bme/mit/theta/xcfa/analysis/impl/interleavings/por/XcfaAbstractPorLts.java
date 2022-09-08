package hu.bme.mit.theta.xcfa.analysis.impl.interleavings.por;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaState;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.util.*;

public final class XcfaAbstractPorLts extends XcfaPorLts {

	private final Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry;

	public XcfaAbstractPorLts(XCFA xcfa, Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry) {
		super(xcfa);
		this.ignoredVariableRegistry = ignoredVariableRegistry;
	}

	@Override
	public <P extends Prec> Collection<XcfaAction> getEnabledActionsFor(XcfaState<?> state, P prec) {
		// Collecting enabled actions
		Collection<XcfaAction> allEnabledActions = getAllEnabledActionsFor(state);

		// Calculating the persistent set starting from every (or some of the) enabled transition; the minimal persistent set is stored
		Collection<XcfaAction> minimalPersistentSet = new HashSet<>();
		Collection<XcfaAction> persistentSetFirstActions = getPersistentSetFirstActions(allEnabledActions);
		Set<Decl<? extends Type>> finalIgnoredVariables = new HashSet<>();
		for (XcfaAction firstAction : persistentSetFirstActions) {
			Set<Decl<? extends Type>> ignoredVariables = new HashSet<>();
			Collection<XcfaAction> persistentSet = calculatePersistentSet(allEnabledActions, firstAction, prec, ignoredVariables);
			if (minimalPersistentSet.size() == 0 || persistentSet.size() < minimalPersistentSet.size()) {
				minimalPersistentSet = persistentSet;
				finalIgnoredVariables = ignoredVariables;
			}
		}

		finalIgnoredVariables.forEach(ignoredVariable -> {
			if (!ignoredVariableRegistry.containsKey(ignoredVariable)) {
				ignoredVariableRegistry.put(ignoredVariable, new HashSet<>());
			}
			ignoredVariableRegistry.get(ignoredVariable).add(state);
		});

		return minimalPersistentSet;
	}

	private Collection<XcfaAction> calculatePersistentSet(Collection<XcfaAction> enabledActions, XcfaAction firstAction, Prec prec, Set<Decl<? extends Type>> ignoredVariables) {
		if (isBackwardAction(firstAction)) {
			return new HashSet<>(enabledActions);
		}

		Set<XcfaAction> persistentSet = new HashSet<>();
		Set<XcfaAction> otherActions = new HashSet<>(enabledActions); // actions not in the persistent set
		persistentSet.add(firstAction);
		otherActions.remove(firstAction);
		Map<XcfaAction, Set<Decl<? extends Type>>> ignoredVariablesByAction = new HashMap<>();
		otherActions.forEach(action -> ignoredVariablesByAction.put(action, new HashSet<>()));

		boolean addedNewAction = true;
		while (addedNewAction) {
			addedNewAction = false;
			Set<XcfaAction> actionsToRemove = new HashSet<>();
			for (XcfaAction action : otherActions) {
				// for every action that is not in the persistent set it is checked whether it should be added to the persistent set
				// (because it is dependent with an action already in the persistent set)
				Set<Decl<? extends Type>> potentialIgnoredVariables = new HashSet<>();
				if (persistentSet.stream().anyMatch(persistentSetAction -> areDependents(persistentSetAction, action, prec, potentialIgnoredVariables))) {
					if (isBackwardAction(action)) {
						return new HashSet<>(enabledActions); // see POR algorithm for the reason of removing backward transitions
					}

					persistentSet.add(action);
					actionsToRemove.add(action);
					addedNewAction = true;
				} else {
					ignoredVariablesByAction.get(action).addAll(potentialIgnoredVariables);
				}
			}
			actionsToRemove.forEach(otherActions::remove);
		}
		otherActions.forEach(action -> ignoredVariables.addAll(ignoredVariablesByAction.get(action)));

		return persistentSet;
	}

	private boolean isIgnorable(Decl<? extends Type> varDecl, Prec prec) {
		Collection<? extends Decl<? extends Type>> usedVars = prec.getUsedVars();
		return !usedVars.contains(varDecl);
	}

	private boolean areDependents(XcfaAction persistentSetAction, XcfaAction action, Prec prec, Set<Decl<? extends Type>> ignoredVariables) {
		if (canEnOrDisableEachOther(persistentSetAction, action)) {
			return true;
		}

		Set<? extends Decl<? extends Type>> usedByPersistentSetAction = getCachedUsedSharedObjects(getTransitionOf(persistentSetAction));
		Set<? extends Decl<? extends Type>> influencedSharedObjects = getInfluencedSharedObjects(getTransitionOf(action));
		for (Decl<? extends Type> varDecl : influencedSharedObjects) {
			if (usedByPersistentSetAction.contains(varDecl)) {
				if (isIgnorable(varDecl, prec)) {
					ignoredVariables.add(varDecl);
					continue;
				}
				return true;
			}
		}
		return false;
	}
}
