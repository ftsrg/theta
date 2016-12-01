package hu.bme.mit.theta.frontend.c.ir.node;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public class AssertNode implements NonTerminatorIrNode {

	private Expr<? extends BoolType> cond;
	private BasicBlock parent;

	public AssertNode(Expr<? extends BoolType> cond) {
		this.cond = cond;
	}

	@Override
	public AssertNode copy() {
		return new AssertNode(this.cond);
	}

	@Override
	public String getLabel() {
		return "Assert(" + this.cond + ")";
	}

	@Override
	public void setParentBlock(BasicBlock block) {
		this.parent = block;
	}

	@Override
	public BasicBlock getParentBlock() {
		return this.parent;
	}

	public Expr<? extends BoolType> getCond() {
		return cond;
	}

	public void setCond(Expr<? extends BoolType> cond) {
		this.cond = cond;
	}

	@Override
	public String toString() {
		return this.getLabel();
	}

}
