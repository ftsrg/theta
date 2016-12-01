package hu.bme.mit.theta.frontend.c.ir.node;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public class AssignNode<VarType extends Type, ExprType extends VarType> implements NonTerminatorIrNode {

	private VarDecl<VarType> var;
	private Expr<? extends Type> expr;

	private BasicBlock parent;

	public AssignNode(VarDecl<VarType> var, Expr<? extends Type> expr) {
		this.var = var;
		this.expr = expr;
	}

	@Override
	public AssignNode<VarType, ExprType> copy() {
		return new AssignNode<>(this.var, this.expr);
	}

	public VarDecl<VarType> getVar() {
		return var;
	}

	public void setVar(VarDecl<VarType> var) {
		this.var = var;
	}

	public Expr<? extends Type> getExpr() {
		return expr;
	}

	public void setExpr(Expr<? extends Type> expr) {
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

	@Override
	public BasicBlock getParentBlock() {
		return this.parent;
	}

	@Override
	public String toString() {
		return this.getLabel();
	}

}
