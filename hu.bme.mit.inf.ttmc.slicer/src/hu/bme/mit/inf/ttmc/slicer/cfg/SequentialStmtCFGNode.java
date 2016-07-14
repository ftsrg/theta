package hu.bme.mit.inf.ttmc.slicer.cfg;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class SequentialStmtCFGNode extends StmtCFGNode {

	private Stmt stmt;

	public SequentialStmtCFGNode(Stmt stmt) {
		this.stmt = stmt;
	}

	@Override
	public Stmt getStmt() { return this.stmt; }

	@Override
	public CFGNode copy() {
		return new SequentialStmtCFGNode(this.stmt);
	}

}
