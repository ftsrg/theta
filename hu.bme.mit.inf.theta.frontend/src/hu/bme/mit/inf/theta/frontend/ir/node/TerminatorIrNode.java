package hu.bme.mit.inf.theta.frontend.ir.node;

import java.util.List;

import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;

public interface TerminatorIrNode extends IrNode {

	/**
	 * Returns a list of this node's targets
	 *
	 * @return A list containing all possible paths from this node
	 */
	public List<BasicBlock> getTargets();

	public void replaceTarget(BasicBlock oldBlock, BasicBlock newBlock);

	@Override
	public TerminatorIrNode copy();

}
