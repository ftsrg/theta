package hu.bme.mit.inf.theta.code.ast;

abstract public class AstNode {
		
	abstract public AstNode[] getChildren();
	
	abstract public AstNode copy();
	
}
