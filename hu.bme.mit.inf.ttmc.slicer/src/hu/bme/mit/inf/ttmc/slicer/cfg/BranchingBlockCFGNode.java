package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.List;

public class BranchingBlockCFGNode extends BlockCFGNode {

	public BranchingBlockCFGNode(List<StmtCFGNode> nodes) {
		super(nodes);
	}

	public CFGNode getThenNode() { return this.children.get(0); } // XXX
	public CFGNode getElseNode() { return this.children.get(1); } // XXX

	public CFGNode getBranchNode() { return this.nodes.get(this.nodes.size() - 1) ; }

}
