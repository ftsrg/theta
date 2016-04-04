package hu.bme.mit.inf.ttmc.code.ast;

import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;

public class VarDeclarationAst extends DeclarationAst {

	private String name;
	private List<DeclaratorAst> declarators;
	
	public VarDeclarationAst(String name) {
		this.name = name;
	}
	
	public String getName() {
		return this.name;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

	@Override
	public <D> D accept(DeclarationVisitor<D> visitor) {
		return visitor.visit(this);
	}
	
}
