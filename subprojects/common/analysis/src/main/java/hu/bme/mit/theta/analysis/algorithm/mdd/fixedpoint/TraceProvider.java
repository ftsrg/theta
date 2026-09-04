/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint;

import com.google.common.collect.Lists;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public final class TraceProvider implements MddGraph.CleanupListener {
    public static boolean verbose = false;

    private final CacheManager<BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>>
            cacheManager = new CacheManager<>(v -> new BinaryOperationCache<>());
    private final MddVariableOrder variableOrder;
    private final SingleStepProvider singleStepProvider;
    private final boolean ownsSingleStepProvider;

    public TraceProvider(final MddVariableOrder variableOrder) {
        this(variableOrder, new SingleStepProvider(variableOrder), true);
    }

    public TraceProvider(
            final MddVariableOrder variableOrder, final SingleStepProvider singleStepProvider) {
        this(variableOrder, singleStepProvider, false);
    }

    private TraceProvider(
            final MddVariableOrder variableOrder,
            final SingleStepProvider singleStepProvider,
            final boolean ownsSingleStepProvider) {
        this.variableOrder = variableOrder;
        this.singleStepProvider = singleStepProvider;
        this.ownsSingleStepProvider = ownsSingleStepProvider;
        this.variableOrder.getMddGraph().registerCleanupListener(this);
    }

    /** Clears the caches and unregisters from the graph so the provider can be collected. */
    public void dispose() {
        clear();
        this.variableOrder.getMddGraph().unregisterCleanupListener(this);
        if (ownsSingleStepProvider) {
            singleStepProvider.clear();
            singleStepProvider.dispose();
        }
    }

    public List<MddHandle> compute(
            MddHandle targetStates,
            AbstractNextStateDescriptor reversedNextStateRelation,
            MddHandle initialStates,
            MddVariableHandle highestAffectedVariable)
            throws InterruptedException {

        MddHandle currentState = targetStates;
        MddHandle alreadyExplored = currentState;
        final Stack<MddHandle> states = new Stack<>();
        states.push(currentState);

        while (MddInterpreter.calculateNonzeroCount(currentState.intersection(initialStates))
                <= 0) {
            if (Thread.interrupted()) {
                System.out.println(
                        "Trace computation interrupted after " + states.size() + " steps.");
                throw new InterruptedException();
            }

            final var newLayer =
                    singleStepProvider
                            .compute(
                                    currentState,
                                    reversedNextStateRelation,
                                    highestAffectedVariable)
                            .minus(alreadyExplored);
            if (MddInterpreter.calculateNonzeroCount(newLayer) > 0) {
                currentState = newLayer.satOne();
                states.push(currentState);
                alreadyExplored = alreadyExplored.union(currentState);
            } else {
                states.pop();
                currentState = states.peek();
            }
        }

        return Lists.reverse(states);
    }

    /**
     * Backward breadth-first layers from {@code targetStates} to the initial states, initial side
     * first; a path picked forward through them is a shortest trace.
     */
    public List<MddHandle> computeBreadthFirst(
            MddHandle targetStates,
            AbstractNextStateDescriptor reversedNextStateRelation,
            MddHandle initialStates,
            MddVariableHandle highestAffectedVariable)
            throws InterruptedException {

        final List<MddHandle> layers = new ArrayList<>();
        MddHandle current = targetStates;
        MddHandle explored = targetStates;
        layers.add(current);
        MddHandle initHit = current.intersection(initialStates);

        while (initHit.isTerminalZero()) {
            if (Thread.interrupted()) {
                System.out.println(
                        "Trace computation interrupted after " + layers.size() + " layers.");
                throw new InterruptedException();
            }
            final MddHandle next =
                    singleStepProvider
                            .compute(current, reversedNextStateRelation, highestAffectedVariable)
                            .minus(explored);
            if (next.isTerminalZero()) {
                throw new IllegalStateException(
                        "backward search exhausted the state space without reaching an initial"
                                + " state");
            }
            explored = explored.union(next);
            current = next;
            layers.add(current);
            initHit = current.intersection(initialStates);
        }

        layers.set(layers.size() - 1, initHit);
        return Lists.reverse(layers);
    }

    @Override
    public void clear() {
        this.cacheManager.clearAll();
    }

    @Override
    public void cleanup() {
        this.cacheManager.forEachCache(
                (cache) ->
                        cache.clearSelectively(
                                (source, ns, result) ->
                                        source.getReferenceCount() == 0
                                                || result.getReferenceCount() == 0));
    }
}
