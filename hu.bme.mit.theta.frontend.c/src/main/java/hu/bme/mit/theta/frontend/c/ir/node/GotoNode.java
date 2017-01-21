package hu.bme.mit.theta.frontend.c.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public class GotoNode implements TerminatorIrNode {

	private BasicBlock target;
	private BasicBlock parent;

	public GotoNode(BasicBlock target) {
		this.target = target;
	}

	@Override
	public TerminatorIrNode copy() {
		return new GotoNode(this.target);
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
		//return "Goto(" + this.target.getName() + ")";
		return "Jump()";
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Collections.singletonList(this.target);
	}

	@Override
	public String toString() {
		return this.getLabel();
	}

	@Override
	public void replaceTarget(BasicBlock oldBlock, BasicBlock newBlock) {
		if (oldBlock == this.target) {
			oldBlock.removeParent(this.parent);
			this.target = newBlock;
			this.target.addParent(this.parent);
		} else {
			throw new IllegalArgumentException(
					"Can only replace an existing block (current target: " + this.target.getName() + ", needed target: "
							+ oldBlock.getName() + ", terminator parent: " + this.parent.getName() + ")");
		}
	}

	@Override
	public void setParentBlock(BasicBlock block) {
		this.parent = block;
		this.target.addParent(this.parent);
	}

	@Override
	public BasicBlock getParentBlock() {
		return this.parent;
	}

}
