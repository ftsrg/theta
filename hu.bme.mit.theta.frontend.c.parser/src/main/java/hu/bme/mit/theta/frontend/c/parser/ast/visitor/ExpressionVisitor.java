package hu.bme.mit.theta.frontend.c.parser.ast.visitor;

import hu.bme.mit.theta.frontend.c.parser.ast.BinaryExpressionAst;
import hu.bme.mit.theta.frontend.c.parser.ast.CastExpressionAst;
import hu.bme.mit.theta.frontend.c.parser.ast.ExpressionListAst;
import hu.bme.mit.theta.frontend.c.parser.ast.FunctionCallExpressionAst;
import hu.bme.mit.theta.frontend.c.parser.ast.LiteralExpressionAst;
import hu.bme.mit.theta.frontend.c.parser.ast.NameExpressionAst;
import hu.bme.mit.theta.frontend.c.parser.ast.UnaryExpressionAst;

public interface ExpressionVisitor<E> {

	public E visit(BinaryExpressionAst ast);

	public E visit(LiteralExpressionAst ast);

	public E visit(NameExpressionAst ast);

	public E visit(FunctionCallExpressionAst ast);

	public E visit(UnaryExpressionAst ast);

	public E visit(ExpressionListAst ast);

	public E visit(CastExpressionAst ast);

}
