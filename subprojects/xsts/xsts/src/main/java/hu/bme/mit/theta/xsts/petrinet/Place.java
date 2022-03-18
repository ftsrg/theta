package hu.bme.mit.theta.xsts.petrinet;

import java.util.ArrayList;
import java.util.List;

public final class Place extends Identified {
	private long initialMarking;
	
	private List<PTArc> outgoingArcs = new ArrayList<>();
	private List<TPArc> incomingArcs = new ArrayList<>();
	
	public Place(final String id) {
		super(id);
	}
	
	public long getInitialMarking() {
		return initialMarking;
	}
	
	public void setInitialMarking(final long initialMarking) {
		this.initialMarking = initialMarking;
	}
	
	public List<PTArc> getOutgoingArcs() {
		return outgoingArcs;
	}
	
	public List<TPArc> getIncomingArcs() {
		return incomingArcs;
	}
	
	@Override
	public String toString() {
		return getId();
	}
}
