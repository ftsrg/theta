package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.ArrayList;
import java.util.List;

public class BlockCFGNode extends CFGNode {

	protected List<StmtCFGNode> nodes = new ArrayList<>();

	public BlockCFGNode(List<StmtCFGNode> nodes) {
		this.nodes = nodes;
	}

	public List<StmtCFGNode> getContainedNodes() {
		return this.nodes;
	}

	@Override
	public String getLabel() {
		StringBuilder sb = new StringBuilder();
		this.nodes.forEach(s -> sb.append(s.getLabel() + "\\n"));
		return sb.toString();
	}

	@Override
	public String toString() {
		return "BLOCK: " + this.getLabel();
	}

	@Override
	public CFGNode copy() {
		return new BlockCFGNode(this.nodes);
	}

}
