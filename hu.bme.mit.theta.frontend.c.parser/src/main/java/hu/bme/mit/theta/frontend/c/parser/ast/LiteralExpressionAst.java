package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.ExpressionVisitor;

public class LiteralExpressionAst extends ExpressionAst {

	private int value;

	public LiteralExpressionAst(int value) {
		this.value = value;
	}

	public int getValue() {
		return this.value;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

	@Override
	public <E> E accept(ExpressionVisitor<E> visitor) {
		return visitor.visit(this);
	}

	@Override
	public LiteralExpressionAst copy() {
		return new LiteralExpressionAst(value);
	}

}
