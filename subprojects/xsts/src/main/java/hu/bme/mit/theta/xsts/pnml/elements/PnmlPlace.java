package hu.bme.mit.theta.xsts.pnml.elements;

public class PnmlPlace extends PnmlNode {

	private final int initialMarkings;

	public PnmlPlace(String name, int initialMarkings) {
		super(name);
		this.initialMarkings = initialMarkings;
	}

	public int getInitialMarkings() {
		return initialMarkings;
	}
}
