package hu.bme.mit.inf.theta.frontend.ir.node;

import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;

public interface IrNode {

	public String getLabel();

	public IrNode copy();

	public void setParentBlock(BasicBlock block);

	public BasicBlock getParentBlock();

}
