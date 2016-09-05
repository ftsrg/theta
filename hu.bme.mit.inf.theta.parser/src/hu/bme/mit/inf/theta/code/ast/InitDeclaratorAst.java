package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.DeclaratorVisitor;

public class InitDeclaratorAst extends DeclaratorAst {

	private InitializerAst initializer;
	
	public InitDeclaratorAst(String name) {
		super(name);
	}
	
	public InitDeclaratorAst(String name, InitializerAst initializer) {
		super(name);
		this.initializer = initializer;
	}
	
	public InitializerAst getInitializer() {
		return this.initializer;
	}
	
	@Override
	public AstNode[] getChildren() {
		if (this.initializer != null)
			return new AstNode[] { this.initializer };
		else
			return new AstNode[] { };
	}

	@Override
	public DeclaratorAst copy() {
		if (initializer != null)
			return new InitDeclaratorAst(this.getName(), this.initializer.copy());
		else
			return new InitDeclaratorAst(this.getName());
	}

	@Override
	public <DR> DR accept(DeclaratorVisitor<DR> visitor) {
		return visitor.visit(this);
	}

	
}
