package hu.bme.mit.theta.frontend.petrinet.model;

public final class TPArc extends Identified {
	private long weight;
	
	private Transition source;
	private Place target;
	
	public TPArc(final String id) {
		super(id);
	}
	
	public long getWeight() {
		return weight;
	}
	
	public void setWeight(final long weight) {
		this.weight = weight;
	}
	
	public Transition getSource() {
		return source;
	}
	
	public void setSource(final Transition source) {
		if (this.source != null) {
			this.source.getOutgoingArcs().remove(this);
		}
		this.source = source;
		if (this.source != null) {
			this.source.getOutgoingArcs().add(this);
		}
	}
	
	public Place getTarget() {
		return target;
	}
	
	public void setTarget(final Place target) {
		if (this.target != null) {
			this.target.getIncomingArcs().remove(this);
		}
		this.target = target;
		if (this.target != null) {
			this.target.getIncomingArcs().add(this);
		}
	}
	
	@Override
	public String toString() {
		return getId() + " (" + source.toString() + "->" + target.toString() + ")";
	}
}
