package hu.bme.mit.inf.ttmc.code.ast;

public class DeclaratorAst extends AstNode {

	private String name;
	private InitializerAst initializer;
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.initializer };
	}

	
}
