package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.ExpressionVisitor;

public class NameExpressionAst extends ExpressionAst {
	
	private String name;
	
	public NameExpressionAst(String name) {
		this.name = name;
	}
	
	public String getName() {
		return this.name;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[]{};
	}
	
	@Override
	public <E> E accept(ExpressionVisitor<E> visitor) {
		return visitor.visit(this);
	}

	@Override
	public NameExpressionAst copy() {
		return new NameExpressionAst(name);
	}

	
}
