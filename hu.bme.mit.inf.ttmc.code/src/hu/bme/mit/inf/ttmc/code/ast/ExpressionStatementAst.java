package hu.bme.mit.inf.ttmc.code.ast;

public class ExpressionStatementAst extends StatementAst {

	private ExpressionAst expr;
	
	public ExpressionStatementAst(ExpressionAst expr) {
		this.expr = expr;
	}
	
	public ExpressionAst getExpression() {
		return this.expr;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.expr };
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
	
	
}
