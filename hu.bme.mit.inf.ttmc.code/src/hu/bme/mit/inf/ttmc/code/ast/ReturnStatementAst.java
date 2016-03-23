package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class ReturnStatementAst extends StatementAst {

	private ExpressionAst expr;
	
	public ReturnStatementAst(ExpressionAst expr) {
		this.expr = expr;
	}

	public ExpressionAst getExpr() {
		return this.expr;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {this.expr};
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}
	
}
