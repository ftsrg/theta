/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;

import java.util.*;
import java.util.function.Predicate;

/**
 * LTS with a POR (Partial Order Reduction) algorithm applied as a filter when returning enabled actions.
 *
 * @param <S> the type of the state
 * @param <A> the type of the action (transition in the state space)
 * @param <T> the type of the transition in the original formalism
 */
public abstract class SporLts<S extends State, A extends Action, T> implements LTS<S, A> {

    /* CACHE COLLECTIONS */

    /**
     * Shared objects (~global variables) used by a transition.
     */
    private final HashMap<T, Set<? extends Decl<? extends Type>>> usedSharedObjects = new HashMap<>();

    /**
     * Shared objects (~global variables) that are used by the key transition or by transitions reachable from the
     * current state via a given transition.
     */
    private final HashMap<T, Set<? extends Decl<? extends Type>>> influencedSharedObjects = new HashMap<>();

    /**
     * Backward transitions in the transition system (a transition of a loop).
     */
    protected final Set<T> backwardTransitions = new LinkedHashSet<>();


    /**
     * Returns the enabled actions in the ARG from the given state filtered with a POR algorithm.
     *
     * @param state the state whose enabled actions we would like to know
     * @return the enabled actions
     */
    @Override
    public Set<A> getEnabledActionsFor(S state) {
        // Collecting enabled actions
        Collection<A> allEnabledActions = getAllEnabledActionsFor(state);

        // Calculating the persistent set starting from every (or some of the) enabled transition; the minimal persistent set is stored
        Set<A> minimalPersistentSet = new LinkedHashSet<>();
        Collection<Collection<A>> persistentSetFirstActions = getPersistentSetFirstActions(allEnabledActions);
        for (Collection<A> firstActions : persistentSetFirstActions) {
            Set<A> persistentSet = calculatePersistentSet(allEnabledActions, firstActions);
            if (minimalPersistentSet.size() == 0 || persistentSet.size() < minimalPersistentSet.size()) {
                minimalPersistentSet = persistentSet;
            }
        }

        return minimalPersistentSet;
    }

    /**
     * Calculates a persistent set of enabled actions starting from a particular action.
     *
     * @param enabledActions the enabled actions in the present state
     * @param firstActions   the actions that will be added to the persistent set as the first actions
     * @return a persistent set of enabled actions
     */
    protected Set<A> calculatePersistentSet(Collection<A> enabledActions, Collection<A> firstActions) {
        if (firstActions.stream().anyMatch(this::isBackwardAction)) {
            return new LinkedHashSet<>(enabledActions);
        }

        Set<A> persistentSet = new LinkedHashSet<>(firstActions);
        Set<A> otherActions = new LinkedHashSet<>(enabledActions); // actions not in the persistent set
        firstActions.forEach(otherActions::remove);

        boolean addedNewAction = true;
        while (addedNewAction) {
            addedNewAction = false;
            Set<A> actionsToRemove = new LinkedHashSet<>();
            for (A action : otherActions) {
                // for every action that is not in the persistent set it is checked whether it should be added to the persistent set
                // (because it is dependent with an action already in the persistent set)
                if (persistentSet.stream().anyMatch(persistentSetAction -> areDependents(persistentSetAction, action))) {
                    if (isBackwardAction(action)) {
                        return new LinkedHashSet<>(enabledActions); // see POR algorithm for the reason of removing backward transitions
                    }

                    persistentSet.add(action);
                    actionsToRemove.add(action);
                    addedNewAction = true;
                }
            }
            actionsToRemove.forEach(otherActions::remove);
        }

        return persistentSet;
    }

    /**
     * Returns all the enabled actions in a state.
     *
     * @param state the state whose enabled actions are to be returned
     * @return the enabled actions in the state
     */
    protected abstract Collection<A> getAllEnabledActionsFor(S state);

    /**
     * Returns the actions from where persistent sets will be calculated (a subset of the given enabled actions).
     * The default implementation returns all enabled actions.
     *
     * @param allEnabledActions all the enabled actions in the present state
     * @return the actions from where persistent sets will be calculated
     */
    protected Collection<Collection<A>> getPersistentSetFirstActions(Collection<A> allEnabledActions) {
        return List.of(allEnabledActions);
    }

    /**
     * Determines whether an action is dependent with another one (based on the notions introduced for the POR
     * algorithm) already in the persistent set.
     *
     * @param persistentSetAction the action in the persistent set
     * @param action              the other action (not in the persistent set)
     * @return true, if the two actions are dependent in the context of persistent sets
     */
    protected boolean areDependents(A persistentSetAction, A action) {
        var usedByPersistentSetAction = getCachedUsedSharedObjects(getTransitionOf(persistentSetAction));
        return isSameProcess(persistentSetAction, action) ||
                getInfluencedSharedObjects(getTransitionOf(action)).stream().anyMatch(usedByPersistentSetAction::contains);
    }

    /**
     * Determines whether two actions are in the same process.
     *
     * @param action1 action 1
     * @param action2 action 2
     * @return true, if the two actions are in the same process
     */
    protected abstract boolean isSameProcess(A action1, A action2);

    /**
     * Determines whether the given action is a backward action.
     *
     * @param action the action to be classified as backward action or non-backward action
     * @return true, if the action is a backward action
     */
    protected boolean isBackwardAction(A action) {
        return backwardTransitions.contains(getTransitionOf(action));
    }

    /**
     * Get the original transition of an action (from which the action has been created).
     *
     * @param action whose original transition is to be returned
     * @return the original transition
     */
    protected abstract T getTransitionOf(A action);

    /**
     * Returns the successive transitions of a transition (transitions whose source is the target of the given
     * parameter).
     *
     * @param transition whose successive transitions is to be returned
     * @return the successive transitions of the transition given as the parameter
     */
    protected abstract Set<T> getSuccessiveTransitions(T transition);


    /**
     * Returns the shared objects (~global variables) that an action uses (it is present in one of its labels).
     *
     * @param transition whose shared objects are to be returned
     * @return the set of used shared objects
     */
    protected abstract Set<? extends Decl<? extends Type>> getDirectlyUsedSharedObjects(T transition);

    /**
     * Returns the shared objects (~global variables) that an action uses.
     *
     * @param transition whose shared objects are to be returned
     * @return the set of directly or indirectly used shared objects
     */
    protected Set<? extends Decl<? extends Type>> getUsedSharedObjects(T transition) {
        return getDirectlyUsedSharedObjects(transition);
    }

    /**
     * Same as {@link SporLts#getUsedSharedObjects(T transition)} with an additional cache layer.
     *
     * @param transition whose shared objects are to be returned
     * @return the set of directly or indirectly used shared objects
     */
    protected Set<? extends Decl<? extends Type>> getCachedUsedSharedObjects(T transition) {
        if (!usedSharedObjects.containsKey(transition)) {
            Set<? extends Decl<? extends Type>> vars = getUsedSharedObjects(transition);
            usedSharedObjects.put(transition, vars);
        }
        return usedSharedObjects.get(transition);
    }

    /**
     * Returns the shared objects (~global variables) used by the given transition or by transitions that are reachable
     * via the given transition ("influenced shared objects").
     *
     * @param transition whose successor transitions' shared objects are to be returned.
     * @return the set of influenced shared objects
     */
    protected Set<? extends Decl<? extends Type>> getInfluencedSharedObjects(T transition) {
        if (!influencedSharedObjects.containsKey(transition)) {
            influencedSharedObjects.put(transition, getSharedObjectsWithBFS(transition, t -> true));
        }
        return influencedSharedObjects.get(transition);
    }

    /**
     * Returns shared objects (~global variables) encountered in a search starting from a given transition.
     *
     * @param startTransition the start point (transition) of the search
     * @param goFurther       the predicate that tells whether more transitions have to be explored through this
     *                        transition
     * @return the set of encountered shared objects
     */
    protected Set<? extends Decl<? extends Type>> getSharedObjectsWithBFS(T startTransition, Predicate<T> goFurther) {
        Set<Decl<? extends Type>> vars = new LinkedHashSet<>();
        List<T> exploredTransitions = new ArrayList<>();
        List<T> transitionsToExplore = new ArrayList<>();
        transitionsToExplore.add(startTransition);

        while (!transitionsToExplore.isEmpty()) {
            T exploring = transitionsToExplore.remove(0);
            vars.addAll(getDirectlyUsedSharedObjects(exploring));

            if (goFurther.test(exploring)) {
                Set<T> successiveTransitions = getSuccessiveTransitions(exploring);
                for (var newTransition : successiveTransitions) {
                    if (!exploredTransitions.contains(newTransition)) {
                        transitionsToExplore.add(newTransition);
                    }
                }
            }
            exploredTransitions.add(exploring);
        }
        return vars;
    }
}
