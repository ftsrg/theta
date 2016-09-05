package hu.bme.mit.inf.theta.code.ast.visitor;

import hu.bme.mit.inf.theta.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.theta.code.ast.ExpressionListAst;
import hu.bme.mit.inf.theta.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.theta.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.theta.code.ast.NameExpressionAst;
import hu.bme.mit.inf.theta.code.ast.UnaryExpressionAst;

public interface ExpressionVisitor<E> {

	public E visit(BinaryExpressionAst ast);
	public E visit(LiteralExpressionAst ast);
	public E visit(NameExpressionAst ast);
	public E visit(FunctionCallExpressionAst ast);
	public E visit(UnaryExpressionAst ast);
	public E visit(ExpressionListAst ast);
	
}
