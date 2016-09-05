package hu.bme.mit.inf.theta.code.ast;

public class AssignmentInitializerAst extends InitializerAst {

	private ExpressionAst expr;
	
	public AssignmentInitializerAst(ExpressionAst expr) {
		this.expr = expr;
	}
	
	@Override
	public AssignmentInitializerAst copy() {
		return new AssignmentInitializerAst(expr.copy());
	}
	
	public ExpressionAst getExpression() {
		return this.expr;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.expr };
	}

}
