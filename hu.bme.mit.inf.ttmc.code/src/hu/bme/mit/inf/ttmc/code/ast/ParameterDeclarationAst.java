package hu.bme.mit.inf.ttmc.code.ast;

public class ParameterDeclarationAst extends AstNode
{
	private DeclarationSpecifierAst specifier;
	private DeclaratorAst declarator;
	
	public ParameterDeclarationAst(DeclarationSpecifierAst specifier, DeclaratorAst declarator) {
		this.specifier = specifier;
		this.declarator = declarator;
	}
	
	public DeclarationSpecifierAst getSpecifier() {
		return this.specifier;
	}
	
	public DeclaratorAst getDeclarator() {
		return this.declarator;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {
			this.specifier,
			this.declarator
		};
	}

	@Override
	public AstNode copy() {
		return new ParameterDeclarationAst(this.specifier.copy(), this.declarator.copy());
	}

}
