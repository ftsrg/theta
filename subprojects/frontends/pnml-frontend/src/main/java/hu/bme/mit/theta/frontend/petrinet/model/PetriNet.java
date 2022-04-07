package hu.bme.mit.theta.frontend.petrinet.model;

import java.util.ArrayList;
import java.util.List;

public final class PetriNet extends Identified {
	private String name;
	
	private List<Place> places = new ArrayList<>();
	private List<Transition> transitions = new ArrayList<>();
	private List<PTArc> ptArcs = new ArrayList<>();
	private List<TPArc> tpArcs = new ArrayList<>();
	
	public PetriNet(final String id) {
		super(id);
	}
	
	public String getName() {
		return name;
	}
	
	public void setName(final String name) {
		this.name = name;
	}
	
	public List<Place> getPlaces() {
		return places;
	}
	
	public List<Transition> getTransitions() {
		return transitions;
	}
	
	public List<PTArc> getPtArcs() {
		return ptArcs;
	}
	
	public List<TPArc> getTpArcs() {
		return tpArcs;
	}
	
	@Override
	public String toString() {
		return getId() + "(" + places.size() + " places, " + transitions.size() + " transitions, " + (ptArcs.size() + tpArcs.size()) + " arcs)";
	}
}
