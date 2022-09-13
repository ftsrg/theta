package hu.bme.mit.theta.analysis.utils;

import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeImpl;
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

import static hu.bme.mit.theta.common.visualization.Alignment.LEFT;
import static hu.bme.mit.theta.common.visualization.Shape.RECTANGLE;

public class MddSymbolicNodeVisualizer {

    private static final LineStyle CHILD_EDGE_STYLE = LineStyle.NORMAL;
    private static final LineStyle DEFAULT_EDGE_STYLE = LineStyle.DOTTED;
    private static final String SYMBOLIC_NODE_LABEL = "";
    private static final String SYMBOLIC_NODE_ID = "symbolicnode";
    private static final String FONT = "courier";
    private static final String NODE_ID_PREFIX = "node_";
    private static final Color FILL_COLOR = Color.WHITE;
    private static final Color LINE_COLOR = Color.BLACK;

    private final Function<MddSymbolicNodeImpl, String> nodeToString;

    private static final Map<MddSymbolicNodeImpl, Long> registry = new IdentityHashMap<>();
    private static long nextId = 0;

    public static long idFor(MddSymbolicNodeImpl n) {
        Long l = registry.get(n);
        if (l == null)
            registry.put(n, l = nextId++);
        return l;
    }

    private static class LazyHolderDefault {
        static final MddSymbolicNodeVisualizer INSTANCE = new MddSymbolicNodeVisualizer(n -> n.toString());
    }

    private static class LazyHolderStructureOnly {
        static final MddSymbolicNodeVisualizer INSTANCE = new MddSymbolicNodeVisualizer(n -> "");
    }

    public MddSymbolicNodeVisualizer(final Function<MddSymbolicNodeImpl, String> nodeToString) {
        this.nodeToString = nodeToString;
    }

    public static MddSymbolicNodeVisualizer create(
            final Function<MddSymbolicNodeImpl, String> nodeToString) {
        return new MddSymbolicNodeVisualizer(nodeToString);
    }

    public static MddSymbolicNodeVisualizer getDefault() {
        return LazyHolderDefault.INSTANCE;
    }

    public static MddSymbolicNodeVisualizer getStructureOnly() {
        return LazyHolderStructureOnly.INSTANCE;
    }

    public Graph visualize(final MddSymbolicNodeImpl rootNode) {
        final Graph graph = new Graph(SYMBOLIC_NODE_ID, SYMBOLIC_NODE_LABEL);

        final Set<MddSymbolicNodeImpl> traversed = Containers.createSet();

        traverse(graph, rootNode, traversed);

        return graph;
    }

    private void traverse(final Graph graph, final MddSymbolicNodeImpl node,
                          final Set<MddSymbolicNodeImpl> traversed) {
        if (traversed.contains(node)) {
            return;
        } else {
            traversed.add(node);
        }
        final String nodeId = NODE_ID_PREFIX + idFor(node);
        final LineStyle lineStyle = CHILD_EDGE_STYLE;
        final int peripheries = node.isComplete()?2:1;

        final NodeAttributes nAttributes = NodeAttributes.builder().label(nodeToString.apply(node))
                .alignment(LEFT).shape(RECTANGLE).font(FONT).fillColor(FILL_COLOR).lineColor(LINE_COLOR)
                .peripheries(peripheries).lineStyle(lineStyle).build();

        graph.addNode(nodeId, nAttributes);

        for(var cur = node.getCacheView().cursor(); cur.moveNext();){
            if(cur.value() != null){
                traverse(graph, cur.value(), traversed);
                final String sourceId = NODE_ID_PREFIX + idFor(node);
                final String targetId = NODE_ID_PREFIX + idFor(cur.value());
                final EdgeAttributes eAttributes = EdgeAttributes.builder().label(cur.key()+"")
                        .alignment(LEFT).font(FONT).color(LINE_COLOR).lineStyle(CHILD_EDGE_STYLE).build();
                graph.addEdge(sourceId, targetId, eAttributes);
            }

        }

        if(node.getCacheView().defaultValue() != null){
            final MddSymbolicNodeImpl defaultValue = node.getCacheView().defaultValue();
            traverse(graph, defaultValue, traversed);
            final String sourceId = NODE_ID_PREFIX + idFor(node);
            final String targetId = NODE_ID_PREFIX + idFor(defaultValue);
            final EdgeAttributes eAttributes = EdgeAttributes.builder()
                    .alignment(LEFT).font(FONT).color(LINE_COLOR).lineStyle(DEFAULT_EDGE_STYLE).build();
            graph.addEdge(sourceId, targetId, eAttributes);
        }
    }

}
