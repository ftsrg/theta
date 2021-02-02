package hu.bme.mit.theta.xsts.pnml.elements;

public class PnmlArc {

	private final int weight;
	private final String id;
	private final PnmlNode sourceNode;
	private final PnmlNode targetNode;

	public PnmlArc(final String id, int weight, final PnmlNode sourceNode, final PnmlNode targetNode) {
		this.id = id;
		this.weight = weight;
		this.sourceNode = sourceNode;
		this.targetNode = targetNode;
	}

	public String getId() { return id; }

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
