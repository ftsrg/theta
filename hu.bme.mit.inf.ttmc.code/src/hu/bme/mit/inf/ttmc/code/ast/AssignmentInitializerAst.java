package hu.bme.mit.inf.ttmc.code.ast;

public class AssignmentInitializerAst extends InitializerAst {

	private ExpressionAst expr;
	
	public AssignmentInitializerAst(ExpressionAst expr) {
		this.expr = expr;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.expr };
	}

}
