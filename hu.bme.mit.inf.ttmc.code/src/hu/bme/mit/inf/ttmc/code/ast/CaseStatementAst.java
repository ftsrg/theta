package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class CaseStatementAst extends StatementAst {

	private ExpressionAst expr;
	
	public CaseStatementAst(ExpressionAst expr) {
		this.expr = expr;
	}

	public CaseStatementAst with(ExpressionAst expr) {
		if (expr == this.expr)
			return this;
		
		return new CaseStatementAst(expr);
	}
	
	
	public ExpressionAst getExpression() {
		return this.expr;
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public StatementAst copy() {
		throw new UnsupportedOperationException();
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.expr };
	}

}
