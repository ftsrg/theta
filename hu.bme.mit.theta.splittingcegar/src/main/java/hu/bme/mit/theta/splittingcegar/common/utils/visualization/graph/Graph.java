package hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

public final class Graph {
	private final String id;
	private final String label;
	private final List<Node> nodes;

	public Graph(final String id, final String label) {
		this.id = checkNotNull(id);
		this.label = checkNotNull(label);
		this.nodes = new ArrayList<>();
	}

	public String getId() {
		return id;
	}

	public String getLabel() {
		return label;
	}

	public List<Node> getNodes() {
		return nodes;
	}

	public void addNode(final Node node) {
		nodes.add(checkNotNull(node));
	}

}
