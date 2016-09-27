package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public class Graph {
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

	public void addNode(final String id, final String label, final Color fillColor, final Color edgeColor,
			final String lineStyle) {
		checkArgument(!nodes.containsKey(id));
		nodes.put(id, new Node(id, label, fillColor, edgeColor, lineStyle));
	}

	public void addCompositeNode(final String id, final String label, final Color fillColor, final Color edgeColor,
			final String lineStyle) {
		checkArgument(!nodes.containsKey(id));
		nodes.put(id, new CompositeNode(id, label, fillColor, edgeColor, lineStyle));
	}

	public void setChild(final String parentId, final String childId) {
		checkArgument(nodes.containsKey(parentId));
		checkArgument(nodes.containsKey(childId));
		final Node parent = nodes.get(parentId);
		checkArgument(parent instanceof CompositeNode);
		((CompositeNode) parent).addChild(nodes.get(childId));
	}

	public void addEdge(final String sourceId, final String targetId, final String label, final Color edgeColor,
			final String lineStyle) {
		checkArgument(nodes.containsKey(sourceId));
		checkArgument(nodes.containsKey(targetId));
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
