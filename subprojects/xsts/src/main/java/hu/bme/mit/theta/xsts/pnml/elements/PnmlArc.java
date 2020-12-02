package hu.bme.mit.theta.xsts.pnml.elements;

public class PnmlArc {

	private final int weight;
	private final PnmlNode sourceNode;
	private final PnmlNode targetNode;

	public PnmlArc(int weight, PnmlNode sourceNode, PnmlNode targetNode) {
		this.weight = weight;
		this.sourceNode = sourceNode;
		this.targetNode = targetNode;
	}

	public int getWeight() {
		return weight;
	}

	public PnmlNode getSourceNode() {
		return sourceNode;
	}

	public PnmlNode getTargetNode() {
		return targetNode;
	}
}
