package hu.bme.mit.inf.ttmc.slicer.cfg;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;

public class BranchStmtCFGNode extends StmtCFGNode {

	private AssumeStmt assume;

	public BranchStmtCFGNode(AssumeStmt assume) {
		this.assume = assume;
	}

	public CFGNode getThenNode() { return this.children.get(0); } // XXX
	public CFGNode getElseNode() { return this.children.get(1); } // XXX

	@Override
	public AssumeStmt getStmt() {
		return this.assume;
	}

	@Override
	public CFGNode copy() {
		return new BranchStmtCFGNode(this.assume);
	}

}
