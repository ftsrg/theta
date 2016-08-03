package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class GotoNode implements TerminatorIrNode {

	private BasicBlock target;
	private BasicBlock parent;

	public GotoNode(BasicBlock target) {
		this.target = target;
	}

	public BasicBlock getTarget() {
		return target;
	}

	public void setTarget(BasicBlock target) {
		this.target.removeParent(this.parent);
		this.target = target;
		this.target.addParent(this.parent);
	}

	@Override
	public String getLabel() {
		return "Goto(" + this.target.getName() + ")";
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

}
