package hu.bme.mit.theta.frontend.c.ir.node;

import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public interface IrNode {

	public String getLabel();

	public IrNode copy();

	public void setParentBlock(BasicBlock block);

	public BasicBlock getParentBlock();

}
