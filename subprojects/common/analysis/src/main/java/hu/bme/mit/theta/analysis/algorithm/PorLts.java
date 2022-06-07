package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;

import java.util.*;

public abstract class PorLts<S extends State, A extends Action> implements LTS<S, A> {

	@Override
	public Collection<A> getEnabledActionsFor(S state) {
		// Collecting enabled edges (with their processes)
		Collection<A> allEnabledActions = getAllEnabledActionsFor(state);

		// Calculating the persistent set starting from every enabled edge; the minimal persistent set is stored
		Collection<A> minimalPersistentSet = new HashSet<>();
		Collection<A> persistentSetFirstActions = getPersistentSetFirstActions(allEnabledActions);
		for (A firstAction : persistentSetFirstActions) {
			Collection<A> persistentSet = calculatePersistentSet(allEnabledActions, firstAction);
			if (minimalPersistentSet.size() == 0 || persistentSet.size() < minimalPersistentSet.size()) {
				minimalPersistentSet = persistentSet;
			}
		}

		return minimalPersistentSet;
	}

	protected Collection<A> calculatePersistentSet(Collection<A> enabledActions, A firstAction) {
		if (isBackwardAction(firstAction)) {
			return new HashSet<>(enabledActions);
		}

		Set<A> persistentSet = new HashSet<>();
		List<A> otherActions = new ArrayList<>(enabledActions); // edges not in the persistent set // TODO: replace List with Set

		persistentSet.add(firstAction);
		otherActions.remove(firstAction);

		boolean addedNewEdge = true;
		while (addedNewEdge) {
			addedNewEdge = false;
			for (int i = 0; i < otherActions.size(); i++) {
				// for every action that is not in the persistent set it is checked whether it should be added to the persistent set
				// (because it is dependent with an action already in the persistent set)
				A action = otherActions.get(i);

				if (persistentSet.stream().anyMatch(persistentSetAction -> areDependents(persistentSetAction, action))) {
					if (isBackwardAction(action)) {
						return new HashSet<>(enabledActions); // to prevent ignoring other threads in "infinite" loops, at least once in every loop (at a backward edge) all enabled edges are returned
					}

					persistentSet.add(action);
					otherActions.remove(action);
					i--;
					addedNewEdge = true;
				}
			}
		}

		return persistentSet;
	}

	protected abstract Collection<A> getAllEnabledActionsFor(S state);

	protected Collection<A> getPersistentSetFirstActions(Collection<A> allEnabledActions) {
		return allEnabledActions;
	}

	protected abstract boolean areDependents(A persistentSetAction, A action);

	protected abstract boolean isBackwardAction(A action);

}
