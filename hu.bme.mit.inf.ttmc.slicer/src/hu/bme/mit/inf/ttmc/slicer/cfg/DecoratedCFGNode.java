package hu.bme.mit.inf.ttmc.slicer.cfg;

public class DecoratedCFGNode extends CFGNode {

	private String name;

	public DecoratedCFGNode(String name) {
		this.name = name;
	}

	@Override
	public String toString() {
		return this.name;
	}

	@Override
	public String getLabel() {
		return this.name;
	}


}
