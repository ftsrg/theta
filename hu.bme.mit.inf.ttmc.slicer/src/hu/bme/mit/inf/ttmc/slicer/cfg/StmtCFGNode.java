package hu.bme.mit.inf.ttmc.slicer.cfg;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public abstract class StmtCFGNode extends CFGNode {

	public abstract Stmt getStmt();

	@Override
	public String getLabel() {
		return this.getStmt().toString();
	}

	@Override
	public String toString() {
		return this.getLabel();
	}

	public static StmtCFGNode fromStmt(Stmt stmt) {
		if (stmt instanceof AssumeStmt) {
			return new BranchStmtCFGNode((AssumeStmt) stmt);
		}

		return new SequentialStmtCFGNode(stmt);
	}

}
