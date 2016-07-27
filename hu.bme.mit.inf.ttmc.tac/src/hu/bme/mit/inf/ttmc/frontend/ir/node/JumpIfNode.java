package hu.bme.mit.inf.ttmc.frontend.ir.node;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class JumpIfNode implements TerminatorIrNode {

	private final Expr<? extends BoolType> cond;
	private final BasicBlock thenTarget;
	private final BasicBlock elseTarget;

	public JumpIfNode(Expr<? extends BoolType> cond, BasicBlock thenTarget, BasicBlock elseTarget) {
		this.cond = cond;
		this.thenTarget = thenTarget;
		this.elseTarget = elseTarget;
	}

	@Override
	public String getLabel() {
		return
		"JumpIf(" +
			this.cond.toString() + ", " +
			this.thenTarget.getName() + ", " +
			this.elseTarget.getName() +
		")";
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

	@Override
	public BasicBlock getDefaultTarget() {
		return this.elseTarget;
	}


}
