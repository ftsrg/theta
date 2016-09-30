package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Edge {

	private final Node source;
	private final Node target;
	private final EdgeAttributes attributes;

	Edge(final Node source, final Node target, final EdgeAttributes attributes) {
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.attributes = checkNotNull(attributes);
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
