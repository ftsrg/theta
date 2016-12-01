package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

public class DoStatementAst extends StatementAst {

	private ExpressionAst cond;
	private StatementAst body;

	public DoStatementAst(ExpressionAst cond, StatementAst body) {
		this.cond = cond;
		this.body = body;
	}

	public DoStatementAst with(ExpressionAst cond, StatementAst body) {
		if (cond == this.cond && body == this.body)
			return this;

		return new DoStatementAst(cond, body);
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

	@Override
	public DoStatementAst copy() {
		return new DoStatementAst(cond.copy(), body.copy());
	}

}
