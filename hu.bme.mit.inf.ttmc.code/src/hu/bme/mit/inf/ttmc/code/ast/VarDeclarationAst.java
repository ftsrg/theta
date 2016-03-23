package hu.bme.mit.inf.ttmc.code.ast;

public class VarDeclarationAst extends AstNode {

	private String name;

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
