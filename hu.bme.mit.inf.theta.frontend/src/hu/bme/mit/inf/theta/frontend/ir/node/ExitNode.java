package hu.bme.mit.inf.theta.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;

public class ExitNode implements TerminatorIrNode {

	private BasicBlock parent;

	@Override
	public TerminatorIrNode copy() {
		return new ExitNode();
	}

	@Override
	public String getLabel() {
		return "exit";
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Collections.emptyList();
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
	public String toString() {
		return this.getLabel();
	}

	@Override
	public void replaceTarget(BasicBlock oldBlock, BasicBlock newBlock) {
		throw new UnsupportedOperationException("Cannot replace an exit block");

	}

}
