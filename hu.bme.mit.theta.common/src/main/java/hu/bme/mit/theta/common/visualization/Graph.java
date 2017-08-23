package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

/**
 * Represents a graph for visualization purposes. It has nodes, composite nodes
 * and directed edges.
 */
public final class Graph {
	private final String id;
	private final String label;
	private final Map<String, Node> nodes;
	private final Collection<Edge> edges;

	/**
	 * Create a new graph instance.
	 *
	 * @param id
	 * @param label
	 */
	public Graph(final String id, final String label) {
		this.id = checkNotNull(id);
		this.label = checkNotNull(label);
		this.nodes = new HashMap<>();
		this.edges = new ArrayList<>();
	}

	/**
	 * Add a new, simple node. The id must not yet exist.
	 *
	 * @param id
	 * @param attributes
	 */
	public void addNode(final String id, final NodeAttributes attributes) {
		checkArgument(!nodes.containsKey(id), "A node with the same id is already present!");
		nodes.put(id, new Node(id, attributes));
	}

	/**
	 * Add a new, composite node. The id must not yet exist.
	 *
	 * @param id
	 * @param attributes
	 */
	public void addCompositeNode(final String id, final NodeAttributes attributes) {
		checkArgument(!nodes.containsKey(id), "A node with the same id is already present!");
		nodes.put(id, new CompositeNode(id, attributes));
	}

	/**
	 * Set a node as a child of another node. Both ids must already exist and
	 * the parent must be composite.
	 *
	 * @param parentId
	 * @param childId
	 */
	public void setChild(final String parentId, final String childId) {
		checkArgument(nodes.containsKey(parentId), "Parent node does not exist!");
		checkArgument(nodes.containsKey(childId), "Child node does not exist!");
		final Node parent = nodes.get(parentId);
		checkArgument(parent instanceof CompositeNode, "Parent node is not composite!");
		((CompositeNode) parent).addChild(nodes.get(childId));
	}

	/**
	 * Add an edge between two nodes. Both ids must already exist.
	 *
	 * @param sourceId
	 * @param targetId
	 * @param attributes
	 */
	public void addEdge(final String sourceId, final String targetId, final EdgeAttributes attributes) {
		checkArgument(nodes.containsKey(sourceId), "Source node does not exist!");
		checkArgument(nodes.containsKey(targetId), "Target node does not exist!");
		final Node source = nodes.get(sourceId);
		final Node target = nodes.get(targetId);
		final Edge edge = new Edge(source, target, attributes);
		edges.add(edge);
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

	public Stream<Node> getRootNodes() {
		return getNodes().stream().filter(Node::isRoot);
	}

	public Collection<Edge> getEdges() {
		return Collections.unmodifiableCollection(edges);
	}
}
