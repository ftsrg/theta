package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.DeclarationVisitor;

public class FunctionDefinitionAst extends DeclarationAst {

	private String name;
	private DeclarationSpecifierAst spec;
	private FunctionDeclaratorAst declarator;
	private CompoundStatementAst body;

	public FunctionDefinitionAst(String name, DeclarationSpecifierAst spec, FunctionDeclaratorAst declarator,
			CompoundStatementAst body) {
		this.name = name;
		this.spec = spec;
		this.declarator = declarator;
		this.body = body;
	}

	public FunctionDefinitionAst with(FunctionDeclaratorAst declarator, CompoundStatementAst body) {
		if (body == this.body && declarator == this.declarator)
			return this;

		return new FunctionDefinitionAst(this.name, this.spec, declarator, body);
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

	@Override
	public FunctionDefinitionAst copy() {
		return new FunctionDefinitionAst(name, this.spec, declarator.copy(), body.copy());
	}

}
