package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents a directed edge of the visualizable graph.
 */
public final class Edge {

	private final Node source;
	private final Node target;
	private final EdgeAttributes attributes;

	/**
	 * Create a new edge. The edge adds itself to the outgoing/incoming edges of
	 * the source/target node.
	 * 
	 * @param source
	 * @param target
	 * @param attributes
	 */
	Edge(final Node source, final Node target, final EdgeAttributes attributes) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.attributes = checkNotNull(attributes);
		source.addOutEdge(this);
		target.addInEdge(this);
	}

	public Node getSource() {
		return source;
	}

	public Node getTarget() {
		return target;
	}

	public EdgeAttributes getAttributes() {
		return attributes;
	}

}
