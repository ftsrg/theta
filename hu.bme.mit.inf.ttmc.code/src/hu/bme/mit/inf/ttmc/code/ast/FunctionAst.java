package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;

public class FunctionAst extends DeclarationAst {

	private String name;
	private CompoundStatementAst body;
	
	public FunctionAst(String name, CompoundStatementAst body) {
		this.name = name;
		this.body = body;
	}

	public CompoundStatementAst getBody() {
		return this.body;		
	}

	public String getName() {
		return this.name;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.body };
	}

	@Override
	public <D> D accept(DeclarationVisitor<D> visitor) {
		return visitor.visit(this);
	}
	
	
}
