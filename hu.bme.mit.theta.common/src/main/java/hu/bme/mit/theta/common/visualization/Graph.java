package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public final class Graph {
	private final String id;
	private final String label;
	private final Map<String, Node> nodes;
	private final Collection<Edge> edges;

	public Graph(final String id, final String label) {
		this.id = checkNotNull(id);
		this.label = checkNotNull(label);
		this.nodes = new HashMap<>();
		this.edges = new ArrayList<>();
	}

	public void addNode(final String id, final String label, final Color fillColor, final Color lineColor,
			final LineStyle lineStyle, final int peripheries) {
		checkArgument(!nodes.containsKey(id), "A node with the same id is already present!");
		nodes.put(id, new Node(id, label, fillColor, lineColor, lineStyle, peripheries));
	}

	public void addCompositeNode(final String id, final String label, final Color fillColor, final Color lineColor,
			final LineStyle lineStyle, final int peripheries) {
		checkArgument(!nodes.containsKey(id), "A node with the same id is already present!");
		nodes.put(id, new CompositeNode(id, label, fillColor, lineColor, lineStyle, peripheries));
	}

	public void setChild(final String parentId, final String childId) {
		checkArgument(nodes.containsKey(parentId), "Parent node does not exist!");
		checkArgument(nodes.containsKey(childId), "Child node does not exist!");
		final Node parent = nodes.get(parentId);
		checkArgument(parent instanceof CompositeNode, "Parent node is not composite!");
		((CompositeNode) parent).addChild(nodes.get(childId));
	}

	public void addEdge(final String sourceId, final String targetId, final String label, final Color edgeColor,
			final LineStyle lineStyle) {
		checkArgument(nodes.containsKey(sourceId), "Source node does not exist!");
		checkArgument(nodes.containsKey(targetId), "Target node does not exist!");
		final Node source = nodes.get(sourceId);
		final Node target = nodes.get(targetId);
		final Edge edge = new Edge(source, target, label, edgeColor, lineStyle);
		edges.add(edge);
		source.addOutEdge(edge);
		target.addInEdge(edge);
	}

	public String getId() {
		return id;
	}

	public String getLabel() {
		return label;
	}

	public Collection<Node> getNodes() {
		return Collections.unmodifiableCollection(nodes.values());
	}

	public Collection<Edge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}
}
