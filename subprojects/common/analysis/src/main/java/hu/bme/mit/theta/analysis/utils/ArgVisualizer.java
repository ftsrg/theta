/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.utils;

import static hu.bme.mit.theta.common.visualization.Alignment.LEFT;
import static hu.bme.mit.theta.common.visualization.Shape.RECTANGLE;

import java.awt.Color;

import hu.bme.mit.theta.common.container.Containers;

import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;

public final class ArgVisualizer<S extends State, A extends Action> implements WitnessVisualizer<ARG<? extends S, ? extends A>> {

    private static final LineStyle COVER_EDGE_STYLE = LineStyle.DASHED;
    private static final LineStyle SUCC_EDGE_STYLE = LineStyle.NORMAL;
    private static final String ARG_LABEL = "";
    private static final String ARG_ID = "arg";
    private static final String FONT = "courier";
    private static final String NODE_ID_PREFIX = "node_";
    private static final Color FILL_COLOR = Color.WHITE;
    private static final Color LINE_COLOR = Color.BLACK;
    private static final String PHANTOM_INIT_ID = "phantom_init";

    private final Function<S, String> stateToString;
    private final Function<A, String> actionToString;

    private static class LazyHolderDefault {

        static final ArgVisualizer<State, Action> INSTANCE = new ArgVisualizer<>(Object::toString,
                Object::toString);
    }

    private static class LazyHolderStructureOnly {

        static final ArgVisualizer<State, Action> INSTANCE = new ArgVisualizer<>(s -> "", a -> "");
    }

    public ArgVisualizer(final Function<S, String> stateToString,
                         final Function<A, String> actionToString) {
        this.stateToString = stateToString;
        this.actionToString = actionToString;
    }

    public static <S extends State, A extends Action> ArgVisualizer<S, A> create(
            final Function<S, String> stateToString, final Function<A, String> actionToString) {
        return new ArgVisualizer<>(stateToString, actionToString);
    }

    public static ArgVisualizer<State, Action> getDefault() {
        return LazyHolderDefault.INSTANCE;
    }

    public static ArgVisualizer<State, Action> getStructureOnly() {
        return LazyHolderStructureOnly.INSTANCE;
    }

    @Override
    public Graph visualize(final ARG<? extends S, ? extends A> arg) {
        final Graph graph = new Graph(ARG_ID, ARG_LABEL);

        final Set<ArgNode<? extends S, ? extends A>> traversed = Containers.createSet();

        for (final ArgNode<? extends S, ? extends A> initNode : arg.getInitNodes()
                .collect(Collectors.toSet())) {
            traverse(graph, initNode, traversed);
            final NodeAttributes nAttributes = NodeAttributes.builder().label("")
                    .fillColor(FILL_COLOR)
                    .lineColor(FILL_COLOR).lineStyle(SUCC_EDGE_STYLE).peripheries(1).build();
            graph.addNode(PHANTOM_INIT_ID + initNode.getId(), nAttributes);
            final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
                    .lineStyle(SUCC_EDGE_STYLE).build();
            graph.addEdge(PHANTOM_INIT_ID + initNode.getId(), NODE_ID_PREFIX + initNode.getId(),
                    eAttributes);
        }

        return graph;
    }

    private void traverse(final Graph graph, final ArgNode<? extends S, ? extends A> node,
                          final Set<ArgNode<? extends S, ? extends A>> traversed) {
        if (traversed.contains(node)) {
            return;
        } else {
            traversed.add(node);
        }
        final String nodeId = NODE_ID_PREFIX + node.getId();
        final LineStyle lineStyle = SUCC_EDGE_STYLE;
        final int peripheries = node.isTarget() ? 2 : 1;

        final NodeAttributes nAttributes = NodeAttributes.builder()
                .label(stateToString.apply(node.getState()))
                .alignment(LEFT).shape(RECTANGLE).font(FONT).fillColor(FILL_COLOR).lineColor(LINE_COLOR)
                .lineStyle(lineStyle).peripheries(peripheries).build();

        graph.addNode(nodeId, nAttributes);

        for (final ArgEdge<? extends S, ? extends A> edge : node.getOutEdges()
                .collect(Collectors.toSet())) {
            traverse(graph, edge.getTarget(), traversed);
            final String sourceId = NODE_ID_PREFIX + edge.getSource().getId();
            final String targetId = NODE_ID_PREFIX + edge.getTarget().getId();
            final EdgeAttributes eAttributes = EdgeAttributes.builder()
                    .label(actionToString.apply(edge.getAction()))
                    .alignment(LEFT).font(FONT).color(LINE_COLOR).lineStyle(SUCC_EDGE_STYLE).build();
            graph.addEdge(sourceId, targetId, eAttributes);
        }

        if (node.getCoveringNode().isPresent()) {
            traverse(graph, node.getCoveringNode().get(), traversed);
            final String sourceId = NODE_ID_PREFIX + node.getId();
            final String targetId = NODE_ID_PREFIX + node.getCoveringNode().get().getId();
            final EdgeAttributes eAttributes = EdgeAttributes.builder().label("").color(LINE_COLOR)
                    .lineStyle(COVER_EDGE_STYLE).weight(0).build();
            graph.addEdge(sourceId, targetId, eAttributes);
        }
    }

}
