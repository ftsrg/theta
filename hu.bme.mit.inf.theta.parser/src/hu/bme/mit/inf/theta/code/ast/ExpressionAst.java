package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.ExpressionVisitor;

abstract public class ExpressionAst extends AstNode {

	abstract public<E> E accept(ExpressionVisitor<E> visitor);
	
	@Override
	abstract public ExpressionAst copy();
	
}
