package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.List;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class BasicBlockCFGNode extends CFGNode {

	private List<Stmt> block;

	public BasicBlockCFGNode(List<Stmt> block) {
		this.block = block;
	}

	@Override
	public String getLabel() {
		StringBuilder sb = new StringBuilder();
		this.block.forEach(s -> sb.append(s + "\\n"));
		return sb.toString();
	}

	@Override
	public String toString() {
		return this.getLabel();
	}

	@Override
	public CFGNode copy() {
		return new BasicBlockCFGNode(this.block);
	}

}
