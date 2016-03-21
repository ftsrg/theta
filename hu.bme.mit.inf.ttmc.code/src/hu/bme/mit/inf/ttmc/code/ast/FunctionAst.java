package hu.bme.mit.inf.ttmc.code.ast;

public class FunctionAst extends AstNode {

	private String name;
	private CompoundStatementAst body;
	
	public FunctionAst(String name, CompoundStatementAst body) {
		this.name = name;
		this.body = body;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.body };
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
	
	
}
