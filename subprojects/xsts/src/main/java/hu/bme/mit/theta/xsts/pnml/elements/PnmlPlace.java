package hu.bme.mit.theta.xsts.pnml.elements;

public class PnmlPlace extends PnmlNode {

	private final int initialMarking;

	public PnmlPlace(final String name, final String id, int initialMarking) {
		super(name,id);
		this.initialMarking = initialMarking;
	}

	public int getInitialMarking() {
		return initialMarking;
	}
}
