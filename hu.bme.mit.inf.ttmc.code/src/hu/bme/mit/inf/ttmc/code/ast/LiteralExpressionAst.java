package hu.bme.mit.inf.ttmc.code.ast;

public class LiteralExpressionAst extends ExpressionAst {

	private int value;
	
	public LiteralExpressionAst(int value) {
		this.value = value;
	}
	
	public int getValue() {
		return this.value;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
