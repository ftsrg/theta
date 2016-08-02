package hu.bme.mit.inf.ttmc.frontend.ir.node;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Variable;

public class AssignNode<VarType extends Type, ExprType extends VarType> implements NonTerminatorIrNode {

	private VarDecl<VarType> var;
	private Expr<ExprType> expr;
	private BasicBlock parent;

	public AssignNode(VarDecl<VarType> var, Expr<ExprType> expr) {
		this.var = var;
		this.expr = expr;
	}

	@Override
	public String getLabel() {
		return "Assign(" + this.var.toString() + ", " + expr.toString() + ")";
	}

	@Override
	public void setParentBlock(BasicBlock block) {
		this.parent = block;
	}

}
