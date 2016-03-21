package hu.bme.mit.inf.ttmc.code.ast;

abstract public class AstNode {
	
	abstract public AstNode[] getChildren();
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
