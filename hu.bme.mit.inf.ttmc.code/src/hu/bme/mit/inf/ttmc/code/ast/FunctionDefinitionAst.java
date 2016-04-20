package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;

public class FunctionDefinitionAst extends DeclarationAst {

	private String name;
	private DeclarationSpecifierAst spec;
	private FunctionDeclaratorAst declarator;
	private CompoundStatementAst body;
	
	public FunctionDefinitionAst(String name, DeclarationSpecifierAst spec, FunctionDeclaratorAst declarator, CompoundStatementAst body) {
		this.name = name;
		this.spec = spec;
		this.declarator = declarator;
		this.body = body;
	}

	public CompoundStatementAst getBody() {
		return this.body;		
	}

	public String getName() {
		return this.name;
	}
	
	public FunctionDeclaratorAst getDeclarator() {
		return this.declarator;
	}

	public DeclarationSpecifierAst getDeclarationSpecifier() {
		return this.spec;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.spec, this.declarator, this.body };
	}

	@Override
	public <D> D accept(DeclarationVisitor<D> visitor) {
		return visitor.visit(this);
	}
	
	public FunctionDefinitionAst copy() {
		return new FunctionDefinitionAst(name, this.spec, declarator.copy(), body.copy());
	}
	
	
}
