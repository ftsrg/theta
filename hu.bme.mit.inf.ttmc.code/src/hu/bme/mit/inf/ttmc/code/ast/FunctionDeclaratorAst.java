package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclaratorVisitor;

public class FunctionDeclaratorAst extends DeclaratorAst {

	public FunctionDeclaratorAst(String name) {
		super(name);
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

	@Override
	public FunctionDeclaratorAst copy() {
		return new FunctionDeclaratorAst(this.getName());
	}

	@Override
	public <DR> DR accept(DeclaratorVisitor<DR> visitor) {
		return visitor.visit(this);
	}
	

}
