package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;

abstract public class ExpressionAst extends AstNode {

	abstract public<E> E accept(ExpressionVisitor<E> visitor);
	
}
