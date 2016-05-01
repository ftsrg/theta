package hu.bme.mit.inf.ttmc.code.ast;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.TranslationUnitVisitor;

public class TranslationUnitAst extends AstNode {

	private List<DeclarationAst> declarations;
	
	public TranslationUnitAst(List<DeclarationAst> declarations) {
		this.declarations = declarations;
	}

	public List<DeclarationAst> getDeclarations() {
		return this.declarations;
	}
	
	@Override
	public AstNode[] getChildren() {
		return this.declarations.toArray(new AstNode[this.declarations.size()]);
	}
	
	public TranslationUnitAst copy() {
		List<DeclarationAst> newDeclarations = new ArrayList<>();
		
		for (DeclarationAst func : this.declarations) {
			newDeclarations.add(func.copy());
		}
		
		return new TranslationUnitAst(newDeclarations);
	}
	
	public<T> T accept(TranslationUnitVisitor<T> visitor) {
		return visitor.visit(this);
	}
	
}
