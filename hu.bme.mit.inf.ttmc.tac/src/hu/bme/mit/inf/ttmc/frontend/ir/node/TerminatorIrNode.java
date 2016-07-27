package hu.bme.mit.inf.ttmc.frontend.ir.node;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public interface TerminatorIrNode extends IrNode {

	/**
	 * Returns this terminator's default target.
	 *
	 * @return A basic block referenced by this terminator
	 */
	public BasicBlock getDefaultTarget();

}
