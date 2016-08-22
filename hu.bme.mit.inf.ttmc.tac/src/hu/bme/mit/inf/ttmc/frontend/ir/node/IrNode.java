package hu.bme.mit.inf.ttmc.frontend.ir.node;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public interface IrNode {

	public String getLabel();

	public IrNode copy();

	public void setParentBlock(BasicBlock block);

	public BasicBlock getParentBlock();

}
