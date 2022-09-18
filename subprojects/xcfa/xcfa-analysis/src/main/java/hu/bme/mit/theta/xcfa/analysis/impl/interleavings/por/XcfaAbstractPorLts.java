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
	public <P extends Prec> Collection<XcfaAction> getEnabledActionsFor(XcfaState<?> state, Collection<XcfaAction> exploredActions, P prec) {
		// Collecting enabled actions
		Collection<XcfaAction> allEnabledActions = getAllEnabledActionsFor(state);

		// Calculating the persistent set starting from every (or some of the) enabled transition or from exploredActions if it is not empty
		// The minimal persistent set is stored
		Collection<XcfaAction> minimalPersistentSet = new HashSet<>();
		final Collection<Collection<XcfaAction>> persistentSetFirstActions = new HashSet<>() {{
			if (exploredActions.isEmpty()) {
				addAll(getPersistentSetFirstActions(allEnabledActions));
			} else {
				add(new ArrayList<>(exploredActions));
			}
		}};
		Set<Decl<? extends Type>> finalIgnoredVariables = new HashSet<>();

		// Calculate persistent sets from all possible starting action set
		for (Collection<XcfaAction> firstActions : persistentSetFirstActions) {
			// Variables that have been ignored (if they would be in the precision, more actions have had to be added to the persistent set)
			Set<Decl<? extends Type>> ignoredVariables = new HashSet<>();
			Collection<XcfaAction> persistentSet = calculatePersistentSet(allEnabledActions, firstActions, prec, ignoredVariables);
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

		minimalPersistentSet.removeAll(exploredActions);
		return minimalPersistentSet;
	}

	/**
	 * Calculates a persistent set of enabled actions starting from a set of particular actions.
	 *
	 * @param enabledActions the enabled actions in the present state
	 * @param firstActions the actions that will be added to the persistent set as the first actions
	 * @param prec the precision of the current abstraction
	 * @param ignoredVariables variables that have been ignored (if they would be in the precision, more actions have had to be added to the persistent set)
	 * @return a persistent set of enabled actions in the current abstraction
	 */
	private Collection<XcfaAction> calculatePersistentSet(Collection<XcfaAction> enabledActions, Collection<XcfaAction> firstActions, Prec prec, Set<Decl<? extends Type>> ignoredVariables) {
		if (firstActions.stream().anyMatch(this::isBackwardAction)) {
			return new HashSet<>(enabledActions);
		}

		Set<XcfaAction> persistentSet = new HashSet<>(firstActions);
		Set<XcfaAction> otherActions = new HashSet<>(enabledActions); // actions not in the persistent set
		firstActions.forEach(otherActions::remove);
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
					ignoredVariablesByAction.get(action).addAll(potentialIgnoredVariables); // the action is not added to the persistent set because we ignore variables in potentialIgnoredVariables
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
				if (isIgnorable(varDecl, prec)) { // the actions would be dependent, but we may have a chance to ignore it in the current abstraction
					ignoredVariables.add(varDecl);
					continue;
				}
				return true;
			}
		}
		return false;
	}
}
