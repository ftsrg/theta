package hu.bme.mit.theta.frontend.c.ir.node;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public class NodeFactory {

	public static <VarType extends Type, ExprType extends VarType> AssignNode<VarType, ExprType> Assign(
			VarDecl<VarType> var, Expr<? extends Type> expr) {
		return new AssignNode<>(var, expr);
	}

	public static AssertNode Assert(Expr<? extends BoolType> condition) {
		return new AssertNode(condition);
	}

	public static JumpIfNode JumpIf(Expr<? extends BoolType> condition, BasicBlock then, BasicBlock elze) {
		return new JumpIfNode(condition, then, elze);
	}

	public static GotoNode Goto(BasicBlock target) {
		return new GotoNode(target);
	}

	public static ReturnNode Return(Expr<? extends Type> expr, BasicBlock exitBlock, BasicBlock parent) {
		return new ReturnNode(expr, exitBlock, parent);
	}

}
