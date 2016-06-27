package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class LabeledStatementAst extends StatementAst {

	private String label;
	private StatementAst stmt;
	
	public LabeledStatementAst(String label, StatementAst stmt) {
		this.label = label;
		this.stmt  = stmt;
	}

	public LabeledStatementAst with(StatementAst stmt) {
		if (stmt == this.stmt)
			return this;
		
		return new LabeledStatementAst(label, stmt);
	}

	public String getLabel() {
		return this.label;
	}
	
	public StatementAst getStatement() {
		return this.stmt;
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public StatementAst copy() {
		return new LabeledStatementAst(label, stmt);
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] { stmt };
	}

}
