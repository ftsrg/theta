package hu.bme.mit.inf.theta.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;

public class ReturnNode implements TerminatorIrNode {

	private Expr<? extends Type> expr;
	private final BasicBlock exitBlock;
	private BasicBlock parent;

	public ReturnNode(Expr<? extends Type> expr, BasicBlock exitBlock, BasicBlock parentBlock) {
		this.expr = expr;
		this.exitBlock = exitBlock;
		this.parent = parentBlock;

		this.exitBlock.addParent(this.parent);
	}

	@Override
	public TerminatorIrNode copy() {
		return new ReturnNode(this.expr, this.exitBlock, this.parent);
	}

	public Expr<? extends Type> getExpr() {
		return this.expr;
	}

	public void setExpr(Expr<? extends Type> expr) {
		this.expr = expr;
	}

	@Override
	public String getLabel() {
		return "Return(" + this.expr.toString() + ")";
	}

	@Override
	public List<BasicBlock> getTargets() {
		return Collections.singletonList(this.exitBlock);
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
	public void replaceTarget(BasicBlock oldBlock, BasicBlock newBlock) {
		throw new UnsupportedOperationException("Cannot replace an exit block");

	}

}
