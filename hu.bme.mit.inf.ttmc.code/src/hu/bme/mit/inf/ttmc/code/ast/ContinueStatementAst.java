package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class ContinueStatementAst extends StatementAst {

	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		throw new UnsupportedOperationException();
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
