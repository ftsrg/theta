package hu.bme.mit.theta.frontend.petrinet.model;

import java.util.ArrayList;
import java.util.List;

public final class Transition extends Identified {
	private List<TPArc> outgoingArcs = new ArrayList<>();
	private List<PTArc> incomingArcs = new ArrayList<>();
	
	public Transition(final String id) {
		super(id);
	}
	
	public List<TPArc> getOutgoingArcs() {
		return outgoingArcs;
	}
	
	public List<PTArc> getIncomingArcs() {
		return incomingArcs;
	}
	
	@Override
	public String toString() {
		return getId();
	}
}
