package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class VarDeclarationStatementAst extends StatementAst {

	private String name;
	
	public VarDeclarationStatementAst(String name) {
		this.name = name;
	}
	
	public String getName() {
		return this.name;
	}
	
	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}
	
	@Override
	public <S> S accept(StatementVisitor<S> visitor) {
		return visitor.visit(this);
	}
	
}
