package hu.bme.mit.inf.ttmc.frontend.ir.node;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

public class ReturnNode implements TerminatorIrNode {

	private Expr<? extends Type> expr;
	private BasicBlock parent;

	public ReturnNode(Expr<? extends Type> expr) {
		this.expr = expr;
	}

	@Override
	public String getLabel() {
		return "Return(" + this.expr.toString() + ")";
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
