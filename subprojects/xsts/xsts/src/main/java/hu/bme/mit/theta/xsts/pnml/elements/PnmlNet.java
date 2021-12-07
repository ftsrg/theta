package hu.bme.mit.theta.xsts.pnml.elements;

import java.util.List;

public class PnmlNet {

	private final List<PnmlPlace> places;
	private final List<PnmlTransition> transitions;

	public PnmlNet(final List<PnmlPlace> places, final List<PnmlTransition> transitions) {
		this.places = places;
		this.transitions = transitions;
	}

	public List<PnmlPlace> getPlaces() {
		return places;
	}

	public List<PnmlTransition> getTransitions() {
		return transitions;
	}
}
