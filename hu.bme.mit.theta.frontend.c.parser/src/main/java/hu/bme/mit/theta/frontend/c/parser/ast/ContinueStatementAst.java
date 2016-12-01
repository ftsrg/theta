package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

public class ContinueStatementAst extends StatementAst {

	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public StatementAst copy() {
		return new ContinueStatementAst();
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

}
