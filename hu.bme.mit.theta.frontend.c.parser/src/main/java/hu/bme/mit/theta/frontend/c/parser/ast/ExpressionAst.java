package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.ExpressionVisitor;

abstract public class ExpressionAst extends AstNode {

	abstract public <E> E accept(ExpressionVisitor<E> visitor);

	@Override
	abstract public ExpressionAst copy();

}
