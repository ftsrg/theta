package hu.bme.mit.inf.ttmc.slicer.cfg;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;

public class BranchingBlockCFGNode extends BlockCFGNode implements BranchingCFGNode {

	public BranchingBlockCFGNode(List<StmtCFGNode> nodes) {
		super(nodes);
	}

	public CFGNode getThenNode() { return this.children.get(0); } // XXX
	public CFGNode getElseNode() { return this.children.get(1); } // XXX

	public StmtCFGNode getBranchNode() { return this.nodes.get(this.nodes.size() - 1) ; }

	@Override
	public AssumeStmt getBranchStmt() {
		// The branching statement is always the last
		return (AssumeStmt) this.nodes.get(this.nodes.size() - 1).getStmt();
	}

}
