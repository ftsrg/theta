package hu.bme.mit.inf.ttmc.code.ast;

public class VarDeclarationAst extends AstNode {

	@Override
	public AstNode[] getChildren() {
		// TODO Auto-generated method stub
		return null;
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
