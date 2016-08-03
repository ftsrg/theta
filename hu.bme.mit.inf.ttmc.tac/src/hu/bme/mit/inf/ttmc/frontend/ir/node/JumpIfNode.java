package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class JumpIfNode implements TerminatorIrNode {

	private Expr<? extends BoolType> cond;
	private BasicBlock thenTarget;
	private BasicBlock elseTarget;
	private BasicBlock parent;

	public JumpIfNode(Expr<? extends BoolType> cond, BasicBlock thenTarget, BasicBlock elseTarget) {
		this.cond = cond;
		this.thenTarget = thenTarget;
		this.elseTarget = elseTarget;
	}

	@Override
	public String getLabel() {
		return
		"Branch(" +
			this.cond.toString() + ", " +
			this.thenTarget.getName() + ", " +
			this.elseTarget.getName() +
		")";
	}

	public void replaceTarget(BasicBlock oldTarget, BasicBlock newTarget) {
		if (this.thenTarget == oldTarget) {
			this.thenTarget = newTarget;
			oldTarget.removeParent(this.parent);
			this.thenTarget.addParent(this.parent);
		} else if (this.elseTarget == oldTarget) {
			this.elseTarget = newTarget;
			oldTarget.removeParent(this.parent);
			this.elseTarget.addParent(this.parent);
		}
	}

	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	public BasicBlock getThenTarget() {
		return thenTarget;
	}

	public BasicBlock getElseTarget() {
		return elseTarget;
	}

	public void setThenTarget(BasicBlock target) {
		this.thenTarget = target;
	}

	public void setElseTarget(BasicBlock target) {
		this.elseTarget = target;
	}

	public void setParent(BasicBlock parent) {
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Arrays.asList(this.thenTarget, this.elseTarget);
	}

	@Override
	public void setParentBlock(BasicBlock block) {
		this.parent = block;
	}


}
