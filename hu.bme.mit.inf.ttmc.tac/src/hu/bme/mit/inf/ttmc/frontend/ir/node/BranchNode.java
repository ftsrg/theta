package hu.bme.mit.inf.ttmc.frontend.ir.node;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public abstract class BranchNode implements IrNode {

	private BasicBlock thenTarget;
	private BasicBlock elseTarget;


}
