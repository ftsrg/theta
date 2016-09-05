package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.StatementVisitor;

public class ForStatementAst extends StatementAst {

	private StatementAst init;
	private ExpressionAst cond;
	private ExpressionAst iter;
	private StatementAst body;
	
	public ForStatementAst(StatementAst init, ExpressionAst cond, ExpressionAst iter, StatementAst body) {
		this.init = init;
		this.cond = cond;
		this.iter = iter;
		this.body = body;
	}

	
	public ForStatementAst with(StatementAst init, ExpressionAst cond, ExpressionAst iter, StatementAst body) {
		if (init == this.init && cond == this.cond && iter == this.iter && body == this.body)
			return this;
		
		return new ForStatementAst(init, cond, iter, body);
	}
	
	public StatementAst getInit() {
		return init;
	}

	public ExpressionAst getCondition() {
		return cond;
	}

	public ExpressionAst getIteration() {
		return iter;
	}
	
	public StatementAst getBody() {
		return this.body;
	}

	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { init, cond, iter, body };
	}

	@Override
	public ForStatementAst copy() {
		return new ForStatementAst(init.copy(), cond.copy(), iter.copy(), body.copy());
	}

}
