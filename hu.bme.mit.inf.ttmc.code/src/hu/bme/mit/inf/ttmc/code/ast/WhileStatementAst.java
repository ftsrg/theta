package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class WhileStatementAst extends StatementAst {

	private ExpressionAst cond;
	private StatementAst body;
	
	public WhileStatementAst(ExpressionAst cond, StatementAst body) {
		this.cond = cond;
		this.body = body;
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { this.cond, this.body };
	}

	public ExpressionAst getCondition() {
		return this.cond;
	}
	
	public StatementAst getBody() {
		return this.body;
	}

}
