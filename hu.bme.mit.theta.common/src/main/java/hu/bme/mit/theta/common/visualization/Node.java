package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

public class Node {

	private final String id;
	private final NodeAttributes attributes;

	private final Collection<Edge> inEdges;
	private final Collection<Edge> outEdges;

	Node(final String id, final NodeAttributes attributes) {
		this.id = checkNotNull(id);
		this.attributes = checkNotNull(attributes);
		this.inEdges = new ArrayList<>();
		this.outEdges = new ArrayList<>();
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

	void addOutEdge(final Edge edge) {
		checkArgument(edge.getSource() == this);
		outEdges.add(edge);
	}

	void addInEdge(final Edge edge) {
		checkArgument(edge.getTarget() == this);
		inEdges.add(edge);
	}
}
