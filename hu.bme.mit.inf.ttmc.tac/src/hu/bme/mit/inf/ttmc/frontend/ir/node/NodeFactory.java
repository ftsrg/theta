package hu.bme.mit.inf.ttmc.frontend.ir.node;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Bool;

public class NodeFactory {

	public static <VarType extends Type, ExprType extends VarType> AssignNode<VarType, ExprType> Assign(
			VarDecl<VarType> var, Expr<ExprType> expr)
	{
		return new AssignNode<VarType, ExprType>(var, expr);
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

	public static ReturnNode Return(Expr<? extends Type> expr) {
		return new ReturnNode(expr);
	}

}
