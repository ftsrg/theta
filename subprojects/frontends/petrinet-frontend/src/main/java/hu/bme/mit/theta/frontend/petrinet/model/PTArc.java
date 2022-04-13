package hu.bme.mit.theta.frontend.petrinet.model;

public final class PTArc extends Identified {
	private boolean isInhibitor;
	private long weight;
	
	private Place source;
	private Transition target;
	
	public PTArc(final String id) {
		super(id);
	}
	
	public boolean isInhibitor() {
		return isInhibitor;
	}
	
	public void setInhibitor(final boolean inhibitor) {
		isInhibitor = inhibitor;
	}
	
	public long getWeight() {
		return weight;
	}
	
	public void setWeight(final long weight) {
		this.weight = weight;
	}
	
	public Place getSource() {
		return source;
	}
	
	public void setSource(final Place source) {
		if (this.source != null) {
			this.source.getOutgoingArcs().remove(this);
		}
		this.source = source;
		if (this.source != null) {
			this.source.getOutgoingArcs().add(this);
		}
	}
	
	public Transition getTarget() {
		return target;
	}
	
	public void setTarget(final Transition target) {
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
