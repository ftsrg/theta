package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.DeclaratorVisitor;

abstract public class DeclaratorAst extends AstNode {

	private String name;

	@Override
	abstract public DeclaratorAst copy();

	abstract public <DR> DR accept(DeclaratorVisitor<DR> visitor);

	public DeclaratorAst(String name) {
		this.name = name;
	}

	public String getName() {
		return this.name;
	}

	protected void setName(String name) {
		this.name = name;
	}

}
