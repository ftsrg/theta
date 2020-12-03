package hu.bme.mit.theta.xsts.pnml.elements;

import java.util.ArrayList;
import java.util.Collection;

public abstract class PnmlNode {

	private final String name;
	private final String id;
	private final Collection<PnmlArc> inArcs;
	private final Collection<PnmlArc> outArcs;

	protected PnmlNode(final String name, final String id) {
		this.name = name;
		this.id = id;
		this.inArcs = new ArrayList<>();
		this.outArcs = new ArrayList<>();
	}

	public String getName() {
		return name;
	}

	public String getId() { return id; }

	public void addInArc(final PnmlArc inArc){
		inArcs.add(inArc);
	}

	public void addOutArc(final PnmlArc outArc){
		outArcs.add(outArc);
	}

	public Collection<PnmlArc> getInArcs() {
		return inArcs;
	}

	public Collection<PnmlArc> getOutArcs() {
		return outArcs;
	}

}
