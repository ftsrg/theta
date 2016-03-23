package hu.bme.mit.inf.ttmc.code.ast;

public class FunctionAst extends AstNode {

	private String name;
	private CompoundStatementAst body;
	
	public FunctionAst(String name, CompoundStatementAst body) {
		this.name = name;
		this.body = body;
	}

	public StatementAst getBody() {
		return this.body;		
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.body };
	}	
	
	
}
