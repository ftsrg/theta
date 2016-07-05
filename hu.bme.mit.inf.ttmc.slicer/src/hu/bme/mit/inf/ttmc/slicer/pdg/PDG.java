package hu.bme.mit.inf.ttmc.slicer.pdg;

import hu.bme.mit.inf.ttmc.slicer.graph.Graph;

public class PDG implements Graph {

	private PDGNode entry;

	public PDG(PDGNode entry)
	{
		this.entry = entry;
	}

	@Override
	public PDGNode getEntry() {
		return entry;
	}
	public void setEntry(PDGNode entry) {
		this.entry = entry;
	}

}
