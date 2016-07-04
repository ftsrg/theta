package hu.bme.mit.inf.ttmc.slicer.cfg;

public class CFG {

	private CFGNode init;
	private CFGNode end;

	public CFG() {}

	public CFG(CFGNode init, CFGNode end) { this.setInit(init); this.setEnd(end); }

	public CFGNode getInit() {
		return init;
	}

	public void setInit(CFGNode init) {
		this.init = init;
	}

	public CFGNode getEnd() {
		return end;
	}

	public void setEnd(CFGNode end) {
		this.end = end;
	}

}
