package hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

public class ClusterNode extends Node {
	private final List<Node> subNodes;

	public ClusterNode(final String id, final String label, final String color, final String fillColor, final String lineStyle, final boolean isInitial) {
		super(id, label, color, fillColor, lineStyle, isInitial);
		subNodes = new ArrayList<Node>();
	}

	public List<Node> getSubNodes() {
		return subNodes;
	}

	public void addSubNode(final Node node) {
		subNodes.add(checkNotNull(node));
	}

}
