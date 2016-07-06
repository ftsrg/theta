package hu.bme.mit.inf.ttmc.slicer.cfg;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class StmtCFGNode extends CFGNode {

	private Stmt stmt;

	public StmtCFGNode(Stmt stmt) {
		this.stmt = stmt;
	}

	public Stmt getStmt() { return this.stmt; }

	@Override
	public String toString() {
		return this.stmt.toString();
	}

	@Override
	public String getLabel() {
		return this.stmt.toString();
	}

	@Override
	public CFGNode copy() {
		return new StmtCFGNode(this.stmt);
	}

}
