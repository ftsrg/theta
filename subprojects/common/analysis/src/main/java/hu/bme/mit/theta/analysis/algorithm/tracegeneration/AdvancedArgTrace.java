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
package hu.bme.mit.theta.analysis.algorithm.tracegeneration;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import java.util.*;
import java.util.stream.Collectors;

class AdvancedArgTrace<S extends State, A extends Action> implements Iterable<ArgNode<S, A>> {
    private static final int HASH_SEED = 7453;
    private volatile int hashCode = 0;

    private final List<ArgNode<S, A>> nodes;
    private final List<ArgEdge<S, A>> edges;
    private final Collection<State> states;

    private AdvancedArgTrace(final ArgNode<S, A> node) {
        // adding items to first index will lead to O(N^2) performance
        final List<ArgNode<S, A>> nodeList = new ArrayList<>();
        final List<ArgEdge<S, A>> edgeList = new ArrayList<>();

        ArgNode<S, A> running = node;
        nodeList.add(running);

        while (running.getInEdge().isPresent()) {
            final ArgEdge<S, A> inEdge = running.getInEdge().get();
            running = inEdge.getSource();
            edgeList.add(inEdge);
            nodeList.add(running);
        }

        // create the correct order by reversing O(N)
        Collections.reverse(nodeList);
        Collections.reverse(edgeList);

        this.nodes = Collections.unmodifiableList(nodeList);
        this.edges = Collections.unmodifiableList(edgeList);
        states = nodes.stream().map(ArgNode::getState).collect(Collectors.toList());
    }

    private AdvancedArgTrace(List<ArgNode<S, A>> nodeList, List<ArgEdge<S, A>> edgeList) {
        this.nodes = Collections.unmodifiableList(nodeList);
        this.edges = Collections.unmodifiableList(edgeList);
        states = nodes.stream().map(ArgNode::getState).collect(Collectors.toList());
    }

    ////

    public static <S extends State, A extends Action> AdvancedArgTrace<S, A> to(
            final ArgNode<S, A> node) {
        checkNotNull(node);
        return new AdvancedArgTrace<>(node);
    }

    public static <S extends State, A extends Action> AdvancedArgTrace<S, A> fromTo(
            final ArgNode<S, A> fromNode, final ArgNode<S, A> toNode) {
        checkNotNull(fromNode);
        checkNotNull(toNode);
        AdvancedArgTrace<S, A> differenceTrace = new AdvancedArgTrace<>(fromNode);
        AdvancedArgTrace<S, A> fullTrace = new AdvancedArgTrace<>(toNode);
        return substituteTrace(fullTrace, differenceTrace);
    }

    /**
     * Substitutes the differenceTrace from the fullTrace, where the differenceTrace should be the
     * beginning of the full trace
     */
    private static <A extends Action, S extends State> AdvancedArgTrace<S, A> substituteTrace(
            AdvancedArgTrace<S, A> fullTrace, AdvancedArgTrace<S, A> differenceTrace) {
        List<ArgNode<S, A>> differenceNodes = differenceTrace.nodes;

        List<ArgNode<S, A>> remainingNodes = new ArrayList<>(fullTrace.nodes);
        remainingNodes.removeIf(
                saArgNode ->
                        !(saArgNode.equals(differenceNodes.get(differenceNodes.size() - 1)))
                                && differenceNodes.contains(saArgNode));

        List<ArgEdge<S, A>> remainingEdges = new ArrayList<>(fullTrace.edges);
        remainingEdges.removeIf(differenceTrace.edges::contains);

        return new AdvancedArgTrace<>(remainingNodes, remainingEdges);
    }

    ////

    /** Gets the length of the trace, i.e., the number of edges. */
    public int length() {
        return edges.size();
    }

    public ArgNode<S, A> node(final int index) {
        return nodes.get(index);
    }

    public ArgEdge<S, A> edge(final int index) {
        return edges.get(index);
    }

    public List<ArgNode<S, A>> nodes() {
        return nodes;
    }

    public List<ArgEdge<S, A>> edges() {
        return edges;
    }

    ////

    /**
     * Converts the ArgTrace to a Trace by extracting states and actions from nodes and edges
     * respectively.
     */
    public Trace<S, A> toTrace() {
        final List<S> states = nodes.stream().map(ArgNode::getState).collect(toList());
        final List<A> actions = edges.stream().map(ArgEdge::getAction).collect(toList());
        return Trace.of(states, actions);
    }

    ////

    @Override
    public Iterator<ArgNode<S, A>> iterator() {
        return nodes.iterator();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AdvancedArgTrace<?, ?> argTrace = (AdvancedArgTrace<?, ?>) o;
        return states.equals(argTrace.states); // && edges.equals(argTrace.edges);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + states.hashCode();
            result = 31 * result + edges.hashCode();
            hashCode = result;
        }
        return result;
        // return Objects.hash(states, edges);
    }
}
