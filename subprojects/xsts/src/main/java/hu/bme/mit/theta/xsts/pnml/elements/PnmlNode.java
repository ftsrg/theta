package hu.bme.mit.theta.xsts.pnml.elements;

import java.util.ArrayList;
import java.util.Collection;

public abstract class PnmlNode {

	private final String name;
	private final Collection<PnmlArc> inArcs;
	private final Collection<PnmlArc> outArcs;

	protected PnmlNode(String name) {
		this.name = name;
		this.inArcs = new ArrayList<>();
		this.outArcs = new ArrayList<>();
	}

	public String getName() {
		return name;
	}

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
