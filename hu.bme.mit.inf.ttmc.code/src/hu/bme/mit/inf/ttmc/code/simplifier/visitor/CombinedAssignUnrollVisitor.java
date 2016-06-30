package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import static hu.bme.mit.inf.ttmc.code.ast.factory.ExpressionAstFactory.Add;
import static hu.bme.mit.inf.ttmc.code.ast.factory.ExpressionAstFactory.Assign;
import static hu.bme.mit.inf.ttmc.code.ast.factory.ExpressionAstFactory.Div;
import static hu.bme.mit.inf.ttmc.code.ast.factory.ExpressionAstFactory.Mod;
import static hu.bme.mit.inf.ttmc.code.ast.factory.ExpressionAstFactory.Mul;
import static hu.bme.mit.inf.ttmc.code.ast.factory.ExpressionAstFactory.Sub;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;

public class CombinedAssignUnrollVisitor extends SimplifyAstVisitor {

	
	@Override
	public ExpressionAst visit(BinaryExpressionAst ast) {
		ExpressionAst left = ast.getLeft().accept(this);
		ExpressionAst right = ast.getRight().accept(this);
		
		switch (ast.getOperator()) {
		case OP_ADD_ASSIGN:
			return Assign(left, Add(left, right));
		case OP_SUB_ASSIGN:
			return Assign(left, Sub(left, right));
		case OP_MUL_ASSIGN:
			return Assign(left, Mul(left, right));
		case OP_DIV_ASSIGN:
			return Assign(left, Div(left, right));
		case OP_MOD_ASSIGN:
			return Assign(left, Mod(left, right));
		default:
			return ast.with(left, right);
		}
	}
	
}
