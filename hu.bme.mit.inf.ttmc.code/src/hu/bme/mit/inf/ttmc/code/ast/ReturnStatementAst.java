package hu.bme.mit.inf.ttmc.code.ast;

public class ReturnStatementAst extends StatementAst {

	private ExpressionAst expr;
	
	public ReturnStatementAst(ExpressionAst expr) {
		this.expr = expr;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {this.expr};
	}
	
	public <R> void accept(AstVisitor<R> visitor) {
		visitor.visit(this);
	}
	
}
