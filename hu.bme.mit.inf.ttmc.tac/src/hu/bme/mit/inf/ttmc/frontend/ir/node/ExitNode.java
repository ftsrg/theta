package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class ExitNode implements TerminatorIrNode {

	private BasicBlock parent;

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

}
