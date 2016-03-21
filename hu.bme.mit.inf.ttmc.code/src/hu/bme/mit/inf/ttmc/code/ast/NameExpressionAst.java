package hu.bme.mit.inf.ttmc.code.ast;

public class NameExpressionAst extends ExpressionAst {
	
	private String name;
	
	public NameExpressionAst(String name) {
		this.name = name;
	}
	
	public String getName() {
		return this.name;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[]{};
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}

	
}
