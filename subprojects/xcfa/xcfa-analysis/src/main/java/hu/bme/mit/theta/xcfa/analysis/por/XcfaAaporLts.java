/*
 *  Copyright 2022 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xcfa.analysis.por;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.util.*;

public final class XcfaAaporLts extends XcfaPorLts {

	private final Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry;

	public XcfaAaporLts(XCFA xcfa, Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry) {
		super(xcfa);
		this.ignoredVariableRegistry = ignoredVariableRegistry;
	}

	@Override
	public <P extends Prec> Set<XcfaAction> getEnabledActionsFor(XcfaState<?> state, Collection<XcfaAction> exploredActions, P prec) {
		// Collecting enabled actions
		Collection<XcfaAction> allEnabledActions = getAllEnabledActionsFor(state);

		// Calculating the persistent set starting from every (or some of the) enabled transition or from exploredActions if it is not empty
		// The minimal persistent set is stored
		Set<XcfaAction> minimalPersistentSet = new LinkedHashSet<>();
		final Collection<Collection<XcfaAction>> persistentSetFirstActions = new LinkedHashSet<>() {{
			if (exploredActions.isEmpty()) {
				addAll(getPersistentSetFirstActions(allEnabledActions));
			} else {
				add(new ArrayList<>(exploredActions));
			}
		}};
		Set<Decl<? extends Type>> finalIgnoredVariables = new LinkedHashSet<>();

		// Calculate persistent sets from all possible starting action set
		for (Collection<XcfaAction> firstActions : persistentSetFirstActions) {
			// Variables that have been ignored (if they would be in the precision, more actions have had to be added to the persistent set)
			Set<Decl<? extends Type>> ignoredVariables = new LinkedHashSet<>();
			Set<XcfaAction> persistentSet = calculatePersistentSet(allEnabledActions, firstActions, prec, ignoredVariables);
			if (minimalPersistentSet.size() == 0 || persistentSet.size() < minimalPersistentSet.size()) {
				minimalPersistentSet = persistentSet;
				finalIgnoredVariables = ignoredVariables;
			}
		}

		finalIgnoredVariables.forEach(ignoredVariable -> {
			if (!ignoredVariableRegistry.containsKey(ignoredVariable)) {
				ignoredVariableRegistry.put(ignoredVariable, new LinkedHashSet<>());
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
	private Set<XcfaAction> calculatePersistentSet(Collection<XcfaAction> enabledActions, Collection<XcfaAction> firstActions, Prec prec, Set<Decl<? extends Type>> ignoredVariables) {
		if (firstActions.stream().anyMatch(this::isBackwardAction)) {
			return new LinkedHashSet<>(enabledActions);
		}

		Set<XcfaAction> persistentSet = new LinkedHashSet<>(firstActions);
		Set<XcfaAction> otherActions = new LinkedHashSet<>(enabledActions); // actions not in the persistent set
		firstActions.forEach(otherActions::remove);
		Map<XcfaAction, Set<Decl<? extends Type>>> ignoredVariablesByAction = new LinkedHashMap<>();
		otherActions.forEach(action -> ignoredVariablesByAction.put(action, new LinkedHashSet<>()));

		boolean addedNewAction = true;
		while (addedNewAction) {
			addedNewAction = false;
			Set<XcfaAction> actionsToRemove = new LinkedHashSet<>();
			for (XcfaAction action : otherActions) {
				// for every action that is not in the persistent set it is checked whether it should be added to the persistent set
				// (because it is dependent with an action already in the persistent set)
				Set<Decl<? extends Type>> potentialIgnoredVariables = new LinkedHashSet<>();
				if (persistentSet.stream().anyMatch(persistentSetAction -> areDependents(persistentSetAction, action, prec, potentialIgnoredVariables))) {
					if (isBackwardAction(action)) {
						return new LinkedHashSet<>(enabledActions); // see POR algorithm for the reason of removing backward transitions
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
