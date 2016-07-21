package hu.bme.mit.inf.ttmc.tac.ir;

public class Goto implements TACNode {

	private int addr;

	public Goto(int addr) {
		this.addr = addr;
	}

	public int getAddress() {
		return this.addr;
	}

	@Override
	public String getLabel() {
		return "Goto(" + this.addr + ")";
	}

}
