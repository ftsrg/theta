/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.algorithm.util.DfsNodeInterface;
import hu.bme.mit.theta.xcfa.alt.algorithm.util.Tracer;
import hu.bme.mit.theta.xcfa.alt.expl.ExplState;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;
import hu.bme.mit.theta.xcfa.alt.transform.DefaultTransformation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

public abstract class XcfaChecker {

    protected XCFA xcfa;
    protected Config config;
    private final Collection<Trace<ExplState, Transition>> finishedTraces;
    protected final Stack<DfsNodeBase> dfsStack = new Stack<>();
    private final Set<ExplState> stackedStates;
    private final Set<ExplState> exploredStates;

    public Collection<Trace<ExplState, Transition>> getTraces() {
        return finishedTraces;
    }

    protected void onFinished(Stack<? extends DfsNodeInterface> dfsStack) {
        if (config.rememberTraces()) {
            finishedTraces.add(Tracer.createTrace(dfsStack));
        }
    }

    protected XcfaChecker(XCFA xcfa, Config config) {
        this.xcfa = xcfa;
        this.config = config;
        if (config.rememberTraces()) {
            finishedTraces = new ArrayList<>();
        } else {
            finishedTraces = null;
        }
        if (rememberStackedStates()) {
            stackedStates = new HashSet<>();
        } else {
            stackedStates = null;
        }
        // TODO rework to rememberExploredStates
        if (discardAlreadyExploredStates()) {
            exploredStates = null;
        } else {
            exploredStates = new HashSet<>();
        }
    }

    public static Config.Builder getSimplePOR() {
        var config = new Config.Builder();
        config.optimizeLocals = true;
        config.partialOrder = true;
        config.ampleSet = true;
        config.discardAlreadyExplored = false;
        config.rememberTraces = false;
        config.debug = false;
        config.forceIterate = false;
        return config;
    }

    public static Config.Builder getSimpleDPOR() {
        var config = new Config.Builder();
        config.optimizeLocals = true;
        config.partialOrder = true;
        config.discardAlreadyExplored = false;
        config.rememberTraces = false;
        config.debug = false;
        config.forceIterate = false;
        return config;
    }

    public static Config.Builder getSimpleExplicit() {
        var config = new Config.Builder();
        config.optimizeLocals = true;
        config.partialOrder = false;
        config.discardAlreadyExplored = true;
        config.rememberTraces = false;
        config.debug = false;
        config.forceIterate = false;
        return config;
    }

    public static XcfaChecker createChecker(XCFA _xcfa, Config config) {
        if (config.forceIterate() && !config.rememberTraces()) {
            System.err.println("Warning! Probably bad configuration");
        }
        if (!config.forceIterate() && config.rememberTraces()) {
            System.err.println("Warning! Probably bad configuration: not all traces will be stored, because program" +
                    "might stop DFS when finding an unsafe property.");
        }
        var xcfa = new DefaultTransformation(_xcfa, config).build();
        if (config.isAmpleSet()) {
            return new POChecker(xcfa, config);
        } else if (config.isPartialOrder()) {
            return new DynamicPOChecker(xcfa, config);
        } else {
            return new ExplicitChecker(xcfa, config);
        }
    }

    private boolean discardAlreadyExploredStates() {
        return config.discardAlreadyExplored();
    }

    protected abstract void onNodePushed(DfsNodeBase node);

    /** Pushes the node to the stack if not explored before */
    private void tryPushNode(DfsNodeBase node) {
        ImmutableExplState state = node.getState();
        if (!discardAlreadyExploredStates()) {
            if (exploredStates.contains(state)) {
                // do not process node
                return;
            }
            exploredStates.add(state);
        }
        if (rememberStackedStates()) {
            stackedStates.add(state);
        }
        dfsStack.push(node);

        onNodePushed(node);
    }

    private void popNode(DfsNodeBase s0) {
        ExplState state = dfsStack.pop().getState();
        if (rememberStackedStates()) {
            stackedStates.remove(state);
        }
        Preconditions.checkState(state.equals(s0.getState()));

    }


    protected abstract DfsNodeBase initialNode(ImmutableExplState state);

    private boolean rememberStackedStates() {
        // TODO create config item for loops
        return true;
    }

    /**
     * Returns whether the given XCFA is safe.
     */
    public final SafetyResult<ExplState, Transition> check() {

        tryPushNode(initialNode(ImmutableExplState.initialState(xcfa)));

        SafetyResult<ExplState, Transition> result = Tracer.safe();

        while (!dfsStack.empty()) {
            DfsNodeBase node = dfsStack.peek();
            if (node.hasChild()) {
                var child = node.child();
                // first check for cycles, then check for explored states
                if (rememberStackedStates() && stackedStates.contains(child.getState())) {
                    node.expand();
                    // expand, do not remove, and retry
                } else {
                    tryPushNode(child);
                }
            } else {

                if (node.isFinished())
                    onFinished(dfsStack);

                if (!node.isSafe()) {
                    // catch first unsafe property found
                    if (config.forceIterate() && result.isSafe()) {
                        result = Tracer.unsafe(dfsStack);
                    } else {
                        return Tracer.unsafe(dfsStack);
                    }
                }
                popNode(node);
            }
        }
        return result;
    }


}
