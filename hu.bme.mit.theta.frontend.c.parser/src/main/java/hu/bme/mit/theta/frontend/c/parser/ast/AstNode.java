package hu.bme.mit.theta.frontend.c.parser.ast;

abstract public class AstNode {

	abstract public AstNode[] getChildren();

	abstract public AstNode copy();

}
