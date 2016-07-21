package hu.bme.mit.inf.ttmc.slicer.cfg;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;

public interface BranchingCFGNode {

	public AssumeStmt getBranchStmt();

}
