package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

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
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}
	
	
	
}
