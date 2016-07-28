package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class GotoNode implements TerminatorIrNode {

	private final BasicBlock target;

	public GotoNode(BasicBlock target) {
		this.target = target;
	}

	public BasicBlock getTarget() {
		return target;
	}

	@Override
	public String getLabel() {
		return "Goto(" + this.target.getName() + ")";
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Collections.singletonList(this.target);
	}

}
