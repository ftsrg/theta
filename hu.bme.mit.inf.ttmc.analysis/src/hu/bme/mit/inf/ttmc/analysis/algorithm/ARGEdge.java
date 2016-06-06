package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;

public class ARGEdge<S extends State, NodeLabel, EdgeLabel> {

	private final ARGNode<S, NodeLabel, EdgeLabel> source;
	private final ARGNode<S, NodeLabel, EdgeLabel> target;

	EdgeLabel label;

	ARGEdge(final ARGNode<S, NodeLabel, EdgeLabel> source, final ARGNode<S, NodeLabel, EdgeLabel> target) {
		this.source = source;
		this.target = target;
	}

	public ARGNode<S, NodeLabel, EdgeLabel> getSource() {
		return source;
	}

	public ARGNode<S, NodeLabel, EdgeLabel> getTarget() {
		return target;
	}

	public EdgeLabel getLabel() {
		return label;
	}

}
