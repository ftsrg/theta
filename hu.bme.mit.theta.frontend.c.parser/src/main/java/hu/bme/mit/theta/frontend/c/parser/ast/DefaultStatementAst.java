package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

public class DefaultStatementAst extends StatementAst {

	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

	@Override
	public StatementAst copy() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

}
