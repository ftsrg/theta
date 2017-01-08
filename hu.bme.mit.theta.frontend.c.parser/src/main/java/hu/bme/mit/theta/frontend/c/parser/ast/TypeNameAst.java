package hu.bme.mit.theta.frontend.c.parser.ast;

import java.util.Optional;

public class TypeNameAst extends AstNode {

	private DeclarationSpecifierAst specifier;
	private Optional<DeclaratorAst> declarator;
	
	public TypeNameAst(DeclarationSpecifierAst specifier, DeclaratorAst declarator) {
		this.specifier = specifier;
		this.declarator = Optional.of(declarator);
	}
	
	public TypeNameAst(DeclarationSpecifierAst specifier) {
		this.specifier = specifier;
		this.declarator = Optional.empty();
	}

	@Override
	public AstNode[] getChildren() {
		if (this.declarator.isPresent()) {
			return new AstNode[] { this.specifier, this.declarator.get() };
		}
		
		return new AstNode[] { this.specifier };
	}

	public DeclarationSpecifierAst getSpecifier() {
		return this.specifier;
	}
	
	public Optional<DeclaratorAst> getDeclarator() {
		return this.declarator;
	}
	
	@Override
	public AstNode copy() {
		throw new UnsupportedOperationException();
	}

}
