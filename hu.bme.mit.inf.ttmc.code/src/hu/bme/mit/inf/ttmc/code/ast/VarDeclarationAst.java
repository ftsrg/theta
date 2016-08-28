package hu.bme.mit.inf.ttmc.code.ast;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;

public class VarDeclarationAst extends DeclarationAst {

	private DeclarationSpecifierAst specifier;
	private List<DeclaratorAst> declarators;
	
	public VarDeclarationAst(DeclarationSpecifierAst specifier, List<DeclaratorAst> declarators) {
		this.specifier = specifier;
		this.declarators = declarators;
	}

	public VarDeclarationAst(DeclarationSpecifierAst specifier, DeclaratorAst declarator) {
		this.specifier = specifier;
		this.declarators = new ArrayList<>();
		this.declarators.add(declarator);
	}
		
	public DeclarationSpecifierAst getSpecifier() {
		return this.specifier;
	}
	
	public List<DeclaratorAst> getDeclarators() {
		return this.declarators;
	}
	
	@Override
	public AstNode[] getChildren() {
		List<AstNode> children = new ArrayList<>();
		children.add(this.specifier);
		for (DeclaratorAst decl : this.declarators) {
			children.add(decl);
		}
		
		return children.toArray(new AstNode[children.size()]);
	}

	@Override
	public <D> D accept(DeclarationVisitor<D> visitor) {
		return visitor.visit(this);
	}

	@Override
	public DeclarationAst copy() {
		List<DeclaratorAst> newDeclarators = new ArrayList<>();
		
		for (DeclaratorAst declarator : this.declarators) {
			newDeclarators.add(declarator.copy());
		}
		
		return new VarDeclarationAst(specifier.copy(), newDeclarators);
	}
	
}
