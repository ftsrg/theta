package hu.bme.mit.inf.ttmc.code.ast.visitor;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;

public interface ExpressionVisitor<E> {

	public E visit(BinaryExpressionAst ast);
	public E visit(LiteralExpressionAst ast);
	public E visit(NameExpressionAst ast);
	public E visit(FunctionCallExpressionAst ast);
	public E visit(UnaryExpressionAst ast);
	
}
