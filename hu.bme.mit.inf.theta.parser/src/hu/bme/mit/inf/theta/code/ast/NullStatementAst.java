package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.StatementVisitor;

public class NullStatementAst extends StatementAst {
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

	@Override
	public NullStatementAst copy() {
		return new NullStatementAst();
	}

	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}

}
