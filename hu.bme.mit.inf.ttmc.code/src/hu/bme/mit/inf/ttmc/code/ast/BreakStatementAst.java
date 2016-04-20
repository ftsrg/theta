package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class BreakStatementAst extends StatementAst {


	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public StatementAst copy() {
		return new BreakStatementAst();
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

}
