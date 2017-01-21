package hu.bme.mit.theta.frontend.c.ir.node;

import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public class SkipNode implements NonTerminatorIrNode  {

	private BasicBlock parent;
	
	@Override
	public String getLabel() {
		return "Skip()";
	}

	@Override
	public void setParentBlock(BasicBlock block) {
		this.parent = block;
	}

	@Override
	public BasicBlock getParentBlock() {
		return this.parent;
	}

	@Override
	public NonTerminatorIrNode copy() {
		return new SkipNode();
	}

}
