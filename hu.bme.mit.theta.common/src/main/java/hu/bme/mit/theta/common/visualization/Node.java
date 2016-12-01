package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

/**
 * Represents a simple node of the visualizable graph.
 */
public class Node {

	private final String id;
	private final NodeAttributes attributes;

	private final Collection<Edge> inEdges;
	private final Collection<Edge> outEdges;

	private Node parent;

	Node(final String id, final NodeAttributes attributes) {
		this.id = checkNotNull(id);
		this.attributes = checkNotNull(attributes);
		this.inEdges = new ArrayList<>();
		this.outEdges = new ArrayList<>();
		this.parent = null;
	}

	public String getId() {
		return id;
	}

	public NodeAttributes getAttributes() {
		return attributes;
	}

	public Collection<Edge> getInEdges() {
		return Collections.unmodifiableCollection(inEdges);
	}

	public Collection<Edge> getOutEdges() {
		return Collections.unmodifiableCollection(outEdges);
	}

	/**
	 * Add an outgoing edge. The source of the edge must be set to this node.
	 *
	 * @param edge
	 */
	void addOutEdge(final Edge edge) {
		checkArgument(edge.getSource() == this, "The source of the edge must be set to this node.");
		outEdges.add(edge);
	}

	/**
	 * Add an incoming edge. The target of the edge must be set to this node.
	 *
	 * @param edge
	 */
	void addInEdge(final Edge edge) {
		checkArgument(edge.getTarget() == this, "The target of the edge must be set to this node.");
		inEdges.add(edge);
	}

	public Node getParent() {
		return parent;
	}

	void setParent(final Node parent) {
		this.parent = parent;
	}

}
