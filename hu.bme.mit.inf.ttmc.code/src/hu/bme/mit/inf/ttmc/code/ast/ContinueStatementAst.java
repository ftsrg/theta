package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

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
