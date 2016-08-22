package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class EntryNode implements TerminatorIrNode {

	private BasicBlock parent;
	private BasicBlock target;

	public EntryNode(BasicBlock target) {
		this.target = target;
	}

	public BasicBlock getTarget() {
		return this.target;
	}

	@Override
	public IrNode copy() {
		return new EntryNode(this.target);
	}

	@Override
	public String getLabel() {
		return "entry";
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Collections.singletonList(this.target);
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

}
