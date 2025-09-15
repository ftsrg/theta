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
package hu.bme.mit.theta.analysis.utils;

import static hu.bme.mit.theta.common.visualization.Alignment.LEFT;
import static hu.bme.mit.theta.common.visualization.Shape.RECTANGLE;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation;
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.common.visualization.EdgeAttributes;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.LineStyle;
import hu.bme.mit.theta.common.visualization.NodeAttributes;
import java.awt.*;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

public class MddNodeCacheVisualizer {

    private static final LineStyle CHILD_EDGE_STYLE = LineStyle.NORMAL;
    private static final LineStyle DEFAULT_EDGE_STYLE = LineStyle.DOTTED;
    private static final String SYMBOLIC_NODE_LABEL = "";
    private static final String SYMBOLIC_NODE_ID = "symbolicnode";
    private static final String FONT = "courier";
    private static final String NODE_ID_PREFIX = "node_";
    private static final Color FILL_COLOR = Color.WHITE;
    private static final Color LINE_COLOR = Color.BLACK;

    private final Function<MddNode, String> nodeToString;

    private static final Map<MddNode, Long> registry = new IdentityHashMap<>();
    private static long nextId = 0;

    public static long idFor(MddNode n) {
        Long l = registry.get(n);
        if (l == null) registry.put(n, l = nextId++);
        return l;
    }

    private static class LazyHolderDefault {
        static final MddNodeCacheVisualizer INSTANCE =
                new MddNodeCacheVisualizer(n -> n.toString());
    }

    private static class LazyHolderStructureOnly {
        static final MddNodeCacheVisualizer INSTANCE = new MddNodeCacheVisualizer(n -> "");
    }

    public MddNodeCacheVisualizer(final Function<MddNode, String> nodeToString) {
        this.nodeToString = nodeToString;
    }

    public static MddNodeCacheVisualizer create(final Function<MddNode, String> nodeToString) {
        return new MddNodeCacheVisualizer(nodeToString);
    }

    public static MddNodeCacheVisualizer getDefault() {
        return LazyHolderDefault.INSTANCE;
    }

    public static MddNodeCacheVisualizer getStructureOnly() {
        return LazyHolderStructureOnly.INSTANCE;
    }

    public Graph visualize(final MddNode rootNode) {
        final Graph graph = new Graph(SYMBOLIC_NODE_ID, SYMBOLIC_NODE_LABEL);

        final Set<MddNode> traversed = Containers.createSet();

        traverse(graph, rootNode, traversed);

        return graph;
    }

    private void traverse(final Graph graph, final MddNode node, final Set<MddNode> traversed) {
        if (traversed.contains(node)) {
            return;
        } else {
            traversed.add(node);
        }
        final String nodeId = NODE_ID_PREFIX + idFor(node);
        final LineStyle lineStyle = CHILD_EDGE_STYLE;

        final int peripheries = 1;
        //        final int peripheries = node.isComplete()?2:1;

        if (node.getRepresentation() instanceof IdentityRepresentation identityRepresentation) {

            final NodeAttributes nAttributes =
                    NodeAttributes.builder()
                            .label(nodeToString.apply(node))
                            .alignment(LEFT)
                            .shape(RECTANGLE)
                            .font(FONT)
                            .fillColor(FILL_COLOR)
                            .lineColor(LINE_COLOR)
                            .peripheries(peripheries)
                            .lineStyle(LineStyle.DASHED)
                            .build();

            graph.addNode(nodeId, nAttributes);

            final MddNode continuation = identityRepresentation.getContinuation();
            traverse(graph, continuation, traversed);

            final String sourceId = NODE_ID_PREFIX + idFor(node);
            final String targetId = NODE_ID_PREFIX + idFor(continuation);
            final EdgeAttributes eAttributes =
                    EdgeAttributes.builder()
                            .alignment(LEFT)
                            .font(FONT)
                            .color(LINE_COLOR)
                            .lineStyle(DEFAULT_EDGE_STYLE)
                            .build();
            graph.addEdge(sourceId, targetId, eAttributes);

        } else {
            final NodeAttributes nAttributes =
                    NodeAttributes.builder()
                            .label(nodeToString.apply(node))
                            .alignment(LEFT)
                            .shape(RECTANGLE)
                            .font(FONT)
                            .fillColor(FILL_COLOR)
                            .lineColor(LINE_COLOR)
                            .peripheries(peripheries)
                            .lineStyle(lineStyle)
                            .build();

            graph.addNode(nodeId, nAttributes);

            if (node.defaultValue() != null) {
                final MddNode defaultValue = node.defaultValue();
                traverse(graph, defaultValue, traversed);

                final String sourceId = NODE_ID_PREFIX + idFor(node);
                final String targetId = NODE_ID_PREFIX + idFor(defaultValue);
                final EdgeAttributes eAttributes =
                        EdgeAttributes.builder()
                                .alignment(LEFT)
                                .font(FONT)
                                .color(LINE_COLOR)
                                .lineStyle(DEFAULT_EDGE_STYLE)
                                .build();
                graph.addEdge(sourceId, targetId, eAttributes);
            } else {
                if (!(node.isTerminal())) {
                    var representation = node.getRepresentation();
                    Preconditions.checkState(representation instanceof MddExpressionRepresentation);
                    var expressionRepresentation = (MddExpressionRepresentation) representation;
                    for (var cursor =
                                    expressionRepresentation
                                            .getExplicitRepresentation()
                                            .getCacheView()
                                            .cursor();
                            cursor.moveNext(); ) {
                        if (cursor.value() != null) {
                            traverse(graph, cursor.value(), traversed);

                            final String sourceId = NODE_ID_PREFIX + idFor(node);
                            final String targetId = NODE_ID_PREFIX + idFor(cursor.value());
                            final EdgeAttributes eAttributes =
                                    EdgeAttributes.builder()
                                            .label(cursor.key() + "")
                                            .alignment(LEFT)
                                            .font(FONT)
                                            .color(LINE_COLOR)
                                            .lineStyle(CHILD_EDGE_STYLE)
                                            .build();
                            graph.addEdge(sourceId, targetId, eAttributes);
                        }
                    }
                }
            }
        }
    }
}
